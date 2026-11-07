"""Tests for nupview. Run with: python -m unittest test_nupview -v

Containers are built here byte by byte from SPEC.md, which also makes it easy
to produce the corrupt and malicious files a real packer never would.
"""

from __future__ import annotations

import hashlib
import io
import os
import struct
import sys
import tempfile
import threading
import unittest
import unittest.mock
from pathlib import Path

import nupview as nv

try:
    from compression import zstd

    compress = zstd.compress
except ImportError:
    import zstandard

    compress = zstandard.ZstdCompressor().compress


def build(tree: dict, *, kind: int = 0, meta: bytes = b"", children_override=None,
          meta_before_blobs: bool = False) -> bytearray:
    """Build a one-package container. `tree` maps names to bytes, dicts, or (bytes, codec)."""
    dirs: list[list] = []
    files: list[dict] = []
    pool = bytearray()

    def intern(name: str) -> tuple[int, int]:
        raw = name.encode()
        pool.extend(raw)
        return len(pool) - len(raw), len(raw)

    def visit(name: str, node: dict) -> int:
        index = len(dirs)
        dirs.append([intern(name), node, []])
        return index

    pending = [visit("", tree)]
    while pending:
        current = pending.pop()
        for name, value in sorted(dirs[current][1].items()):
            if isinstance(value, dict):
                child = visit(name, value)
                dirs[current][2].append(("d", child))
                pending.append(child)
            else:
                data, codec = value if isinstance(value, tuple) else (value, 0)
                files.append({"name": intern(name), "data": data, "codec": codec})
                dirs[current][2].append(("f", len(files) - 1))

    slots: list[int] = []
    dir_records = bytearray()
    for name, _node, kids in dirs:
        first = len(slots)
        slots += [i if k == "d" else len(dirs) + i for k, i in kids]
        dir_records += struct.pack("<IIIIQ", *name, first, len(kids), 0)
    if children_override is not None:
        slots = children_override(slots, len(dirs))

    toc_size = (0x30 + 0x40 + len(dirs) * 0x18 + len(files) * 0x50 + len(slots) * 4 + len(pool))
    inline = meta if meta_before_blobs else b""
    blob_offset = (0x80 + toc_size + len(inline) + 15) & ~15
    blob = bytearray()
    file_records = bytearray()
    for item in files:
        data, codec = item["data"], item["codec"]
        stored = compress(data) if codec == 1 else data
        offset = 0
        if data:
            offset = blob_offset + len(blob)
            blob += stored + bytes(-len(stored) % 16)
        else:
            stored, codec = b"", 0
        file_records += struct.pack("<IIQQQ32sBBH12x", *item["name"], len(data), offset,
                                    len(stored), hashlib.sha256(data).digest(), codec, 0, 0)

    trailing = b"" if inline else meta
    meta_offset = 0x80 + toc_size if inline else (blob_offset + len(blob) if meta else 0)
    package = struct.pack("<QIIIIBBHIQI20x", 0x0100000000010000, 0, nv.NO_DIR, nv.NO_DIR,
                          0x10000, kind, 0, 0, 0, meta_offset, len(meta))
    pool_off = 0x30 + 0x40 + len(dir_records) + len(file_records) + len(slots) * 4
    toc = (struct.pack("<4sIQQQQQ", b"TOC\x01", 1, len(dirs), len(files), pool_off, len(pool), 0)
           + package + dir_records + file_records
           + struct.pack(f"<{len(slots)}I", *slots) + pool)
    assert len(toc) == toc_size
    total = blob_offset + len(blob) + len(trailing)
    head = struct.pack("<4sHHQQ32sQQII16s32s", b"NUP\x01", 0x80, 1, 0x80, len(toc),
                       hashlib.sha256(toc).digest(), blob_offset, total, 1, 0, bytes(16), bytes(32))
    padding = bytes(blob_offset - 0x80 - len(toc) - len(inline))
    return bytearray(head + toc + inline + padding + blob + trailing)


def tlv(records: dict[int, bytes]) -> bytes:
    return b"".join(struct.pack("<HHI", t, 0, len(v)) + v for t, v in sorted(records.items()))


class Base(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.tmp = Path(temp.name)
        self.out = self.tmp / "out"

    def write(self, data: bytes, name: str = "t.nup") -> str:
        path = self.tmp / name
        path.write_bytes(data)
        return str(path)

    def extract_all(self, nup: nv.NupFile, **kwargs) -> nv.Result:
        plan = nv.build_plan(nup, str(self.out), [nv.Target(True, nup.packages[0].root_dir)])
        return nv.run_plan(nup, plan, **kwargs)

    def outside_files(self) -> set[str]:
        """Everything on disk that is not the output folder or the input."""
        return {p.name for p in self.tmp.iterdir()} - {"out", "t.nup"}


class Reading(Base):
    TREE = {"exefs": {"main": b"\x00MAIN" * 50},
            "romfs": {"a.txt": (b"hello " * 1000, 1), "empty.bin": b"",
                      "nested": {"deep": {"日本語.dat": (b"\xff\x00" * 500, 1)}},
                      "no_files": {}}}

    def test_tree_and_paths(self) -> None:
        nup = nv.NupFile(self.write(build(self.TREE)))
        paths = {"/".join(p) for p, is_dir, _ in nup.walk(nup.packages[0].root_dir) if not is_dir}
        self.assertEqual(paths, {"exefs/main", "romfs/a.txt", "romfs/empty.bin",
                                 "romfs/nested/deep/日本語.dat"})

    def test_extract_matches_content_with_empty_dirs(self) -> None:
        nup = nv.NupFile(self.write(build(self.TREE)))
        result = self.extract_all(nup)
        self.assertEqual((result.written, result.failures), (4, []))
        self.assertEqual((self.out / "romfs/a.txt").read_bytes(), b"hello " * 1000)
        self.assertEqual((self.out / "romfs/nested/deep/日本語.dat").read_bytes(), b"\xff\x00" * 500)
        self.assertEqual((self.out / "romfs/empty.bin").read_bytes(), b"")
        self.assertTrue((self.out / "romfs/no_files").is_dir())
        self.assertEqual(list(self.out.rglob("*.nupart")), [])

    def test_large_file_is_streamed_across_chunks(self) -> None:
        data = os.urandom(1000) * 5000  # 5 MB, several read chunks
        nup = nv.NupFile(self.write(build({"big": (data, 1)})))
        self.extract_all(nup)
        self.assertEqual((self.out / "big").read_bytes(), data)

    def test_preview_stops_at_limit(self) -> None:
        nup = nv.NupFile(self.write(build({"big": (b"x" * 3_000_000, 1)})))
        self.assertEqual(nup.read_head(nup.file(0), 100), b"x" * 100)

    def test_resolve(self) -> None:
        nup = nv.NupFile(self.write(build(self.TREE)))
        pkg = nup.packages[0]
        self.assertTrue(nup.resolve(pkg, "romfs/nested")[0])
        self.assertFalse(nup.resolve(pkg, "romfs/a.txt")[0])
        self.assertIsNone(nup.resolve(pkg, "romfs/a.txt/x"))
        self.assertIsNone(nup.resolve(pkg, "nope"))

    def test_existing_files_skipped_unless_overwrite(self) -> None:
        nup = nv.NupFile(self.write(build({"f": b"new"})))
        self.out.mkdir()
        (self.out / "f").write_bytes(b"old")
        self.assertEqual(self.extract_all(nup).skipped, 1)
        self.assertEqual((self.out / "f").read_bytes(), b"old")
        self.extract_all(nup, overwrite=True)
        self.assertEqual((self.out / "f").read_bytes(), b"new")

    def test_cancel_leaves_no_partial_file(self) -> None:
        nup = nv.NupFile(self.write(build({"a": os.urandom(3 << 20), "b": b"later"})))
        cancel = threading.Event()
        result = self.extract_all(nup, cancel=cancel, progress=lambda *_: cancel.set())
        self.assertTrue(result.cancelled)
        self.assertEqual([p for p in self.out.rglob("*") if p.is_file()], [])


class Metadata(Base):
    def spec_records(self) -> dict[int, bytes]:
        loc = bytes([2]) + b"ja" + struct.pack("<I", 6) + "日本".encode()
        return {nv.TLV_DISPLAY_VERSION: b"1.2.3", nv.TLV_TITLE_NAME: b"Super Game",
                nv.TLV_PUBLISHER: b"Acme", nv.TLV_BUILD_ID: b"\xab" * 20 + bytes(12),
                nv.TLV_SOURCE_DUMP: b"dump", nv.TLV_LOCALIZED_TITLES: loc}

    def check(self, nup: nv.NupFile) -> None:
        pkg = nup.packages[0]
        self.assertEqual(pkg.meta.text(nv.TLV_TITLE_NAME), "Super Game")
        self.assertEqual(pkg.meta.text(nv.TLV_PUBLISHER), "Acme")
        self.assertEqual(pkg.meta.text(nv.TLV_SOURCE_DUMP), "dump")
        self.assertEqual(pkg.version_label, "1.2.3")
        self.assertEqual(pkg.meta.titles, {"ja": "日本"})

    def test_spec_ids(self) -> None:
        self.check(nv.NupFile(self.write(build({"f": b"x"}, meta=tlv(self.spec_records())))))

    def test_off_by_one_ids_from_current_upstream(self) -> None:
        shifted = {t - 1: v for t, v in self.spec_records().items()}
        self.check(nv.NupFile(self.write(build({"f": b"x"}, meta=tlv(shifted)))))

    def test_bad_metadata_does_not_block_extraction(self) -> None:
        bad = struct.pack("<HHI", nv.TLV_TITLE_NAME, 0, 9999) + b"short"
        nup = nv.NupFile(self.write(build({"f": b"x"}, meta=bad)))
        self.assertIn("overruns", nup.packages[0].meta.problem)
        self.assertEqual(self.extract_all(nup).written, 1)


class Rejection(Base):
    def assert_rejected(self, data: bytes, message: str) -> None:
        with self.assertRaisesRegex(nv.NupError, message):
            nv.NupFile(self.write(bytes(data)))

    def test_bad_inputs(self) -> None:
        good = build({"f": b"x"})
        self.assert_rejected(b"", "too short")
        self.assert_rejected(b"PK\x03\x04" + bytes(200), "bad magic")
        self.assert_rejected(b"NUP\x02" + good[4:], "major version")
        self.assert_rejected(good[:-1], "size mismatch")
        flagged = bytearray(good)
        flagged[0x4C] = 1
        self.assert_rejected(flagged, "unknown container flags")
        corrupt = bytearray(good)
        corrupt[0x90] ^= 1
        self.assert_rejected(corrupt, "checksum")

    def test_unused_children_slots_are_accepted(self) -> None:
        # Some packers leave padding in the children array; its contents must be ignored.
        data = build({"romfs": {"a": b"1", "b": b"22"}},
                     children_override=lambda slots, _n: slots + [0xFFFFFFFF, 0xFFFFFFFF])
        nup = nv.NupFile(self.write(bytes(data)))
        result = self.extract_all(nup)
        self.assertEqual((result.written, result.failures), (2, []))
        self.assertEqual((self.out / "romfs/b").read_bytes(), b"22")

    def test_child_range_past_the_array_is_rejected(self) -> None:
        def overflow(slots, _n):
            return slots  # the root claims more children than the array holds
        data = build({"a": b"1"}, children_override=overflow)
        toc_size = struct.unpack_from("<Q", data, 0x10)[0]
        toc = bytearray(data[0x80:0x80 + toc_size])
        struct.pack_into("<I", toc, 0x30 + 0x40 + 0xC, 5)  # root child_count
        data[0x80:0x80 + toc_size] = toc
        data[0x18:0x38] = hashlib.sha256(toc).digest()
        self.assert_rejected(data, "child range out of bounds")

    def test_unknown_codec_rejected(self) -> None:
        data = build({"f": b"x"})
        toc_size = struct.unpack_from("<Q", data, 0x10)[0]
        toc = bytearray(data[0x80:0x80 + toc_size])
        toc[0x30 + 0x40 + 0x18 + 0x40] = 2  # lz4: reserved in v1
        data[0x80:0x80 + toc_size] = toc
        data[0x18:0x38] = hashlib.sha256(toc).digest()
        self.assert_rejected(data, "unknown codec")

    def test_corrupt_content_is_reported_and_removed(self) -> None:
        data = build({"bad": b"A" * 64, "good": b"B" * 64})
        blob = struct.unpack_from("<Q", data, 0x38)[0]
        data[blob] ^= 0xFF
        result = self.extract_all(nv.NupFile(self.write(bytes(data))))
        self.assertEqual(result.written, 1)
        self.assertIn("SHA-256", result.failures[0][1])
        self.assertFalse((self.out / "bad").exists())
        self.assertTrue((self.out / "good").exists())

    def test_corrupt_zstd_is_reported(self) -> None:
        data = build({"z": (os.urandom(50) * 200, 1)})
        blob = struct.unpack_from("<Q", data, 0x38)[0]
        data[blob:blob + 4] = b"\0\0\0\0"
        result = self.extract_all(nv.NupFile(self.write(bytes(data))))
        self.assertEqual(result.written, 0)
        self.assertEqual(len(result.failures), 1)

    def test_directory_loop_is_detected(self) -> None:
        # Point the root's only child back at the root.
        data = build({"sub": {}}, children_override=lambda slots, _n: [0])
        nup = nv.NupFile(self.write(bytes(data)))
        with self.assertRaisesRegex(nv.NupError, "directory loop"):
            list(nup.walk(0))


class MaliciousNames(Base):
    def test_traversal_names_cannot_escape_output(self) -> None:
        for name in ("..", "../evil.txt", "..\\evil.txt", "/abs/evil.txt", "C:\\evil.txt",
                     "a/../../evil.txt"):
            with self.subTest(name=name):
                nup = nv.NupFile(self.write(build({name: b"pwned", "ok": b"fine"})))
                result = self.extract_all(nup, overwrite=True)
                self.assertEqual(self.outside_files(), set())
                self.assertEqual(len(result.failures), 1)
                self.assertEqual((self.out / "ok").read_bytes(), b"fine")

    def test_traversal_directory_cannot_escape_output(self) -> None:
        nup = nv.NupFile(self.write(build({"..": {"evil.txt": b"pwned"}})))
        result = self.extract_all(nup)
        self.assertEqual(self.outside_files(), set())
        self.assertEqual(result.written, 0)

    @unittest.skipUnless(os.name == "nt", "Windows naming rules")
    def test_windows_special_names_are_neutralized(self) -> None:
        names = {"CON": b"1", "nul.txt": b"2", "a:stream": b"3", "dots...": b"4", "q?.bin": b"5"}
        result = self.extract_all(nv.NupFile(self.write(build(dict(names)))))
        self.assertEqual((result.written, result.renamed, result.failures), (5, 5, []))
        self.assertEqual({p.name for p in self.out.iterdir()},
                         {"_CON", "_nul.txt", "a_stream", "dots", "q_.bin"})

    @unittest.skipUnless(os.name == "nt", "case-insensitive filesystem")
    def test_case_collision_keeps_first_and_reports_second(self) -> None:
        result = self.extract_all(nv.NupFile(self.write(build({"A.bin": b"1", "a.bin": b"2"}))))
        self.assertEqual(result.written, 1)
        self.assertIn("already uses", result.failures[0][1])

    @unittest.skipUnless(os.name == "nt", "Windows path limit")
    def test_paths_over_260_characters(self) -> None:
        tree: dict = {"file.bin": b"deep"}
        for _ in range(12):
            tree = {"d" * 40: tree}
        result = self.extract_all(nv.NupFile(self.write(build(tree))))
        self.assertEqual((result.written, result.failures), (1, []))


class SetIcon(Base):
    ICON = b"\xff\xd8\xff\xe0" + b"new-icon" * 20
    META = {nv.TLV_DISPLAY_VERSION: b"1.2.3", nv.TLV_TITLE_NAME: b"Game", nv.TLV_ICON: b"\xff\xd8old",
            nv.TLV_BUILD_ID: b"\xab" * 20 + bytes(12), nv.TLV_SOURCE_DUMP: b"dump", 0x8000: b"vendor"}
    TREE = {"romfs": {"a.bin": (b"hello" * 500, 1), "b.bin": b"raw bytes", "empty": b""}}

    def contents(self, path: str) -> dict:
        nup = nv.NupFile(path)
        with open(path, "rb") as fh:
            return {"/".join(p): b"".join(nup.iter_content(nup.file(i), fh))
                    for p, d, i in nup.walk(nup.packages[0].root_dir) if not d}

    def test_replaces_icon_and_keeps_everything_else(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        before = self.contents(path)
        nv.set_icon(path, self.ICON)
        nup = nv.NupFile(path)
        self.assertEqual(nup.packages[0].meta.records, {**self.META, nv.TLV_ICON: self.ICON})
        self.assertEqual(self.contents(path), before)
        self.assertEqual(self.extract_all(nup).failures, [])  # per-file SHA-256 still passes

    def test_repeated_edits_do_not_grow_the_file(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        nv.set_icon(path, self.ICON)
        size = os.path.getsize(path)
        nv.set_icon(path, self.ICON)
        self.assertEqual(os.path.getsize(path), size)

    def test_adds_icon_when_package_has_no_metadata(self) -> None:
        path = self.write(build(self.TREE))
        nv.set_icon(path, self.ICON)
        self.assertEqual(nv.NupFile(path).packages[0].meta.records[nv.TLV_ICON], self.ICON)

    def test_keeps_off_by_one_ids(self) -> None:
        shifted = {t - 1 if t < 0x100 else t: v for t, v in self.META.items()}
        path = self.write(build(self.TREE, meta=tlv(shifted)))
        nv.set_icon(path, self.ICON)
        nup = nv.NupFile(path)
        self.assertEqual(nup.packages[0].meta.records, {**self.META, nv.TLV_ICON: self.ICON})
        with open(path, "rb") as fh:  # stored under the file's own numbering
            fh.seek(nup.packages[0].meta_offset)
            raw = dict(nv._split_tlvs(fh.read(nup.packages[0].meta_size)))
        self.assertEqual(raw[nv.TLV_ICON - 1], self.ICON)
        self.assertEqual(raw[nv.TLV_ICON], b"1.2.3")  # ID 3 is the display version in these files

    def test_removes_localized_icons(self) -> None:
        loc = bytes([2]) + b"ja" + struct.pack("<I", 3) + b"\xff\xd8x"
        path = self.write(build(self.TREE, meta=tlv({**self.META, nv.TLV_LOCALIZED_ICONS: loc})))
        self.assertEqual(nv.set_icon(path, self.ICON).removed_localized, 1)
        self.assertEqual(nv.NupFile(path).packages[0].meta.icons, {})

    def test_output_leaves_original_untouched(self) -> None:
        data = bytes(build(self.TREE, meta=tlv(self.META)))
        path, new = self.write(data), str(self.tmp / "new.nup")
        nv.set_icon(path, self.ICON, output=new)
        self.assertEqual(Path(path).read_bytes(), data)
        self.assertEqual(nv.NupFile(new).packages[0].meta.records[nv.TLV_ICON], self.ICON)
        with self.assertRaisesRegex(nv.NupError, "already exists"):
            nv.set_icon(path, self.ICON, output=new)
        nv.set_icon(path, self.ICON + b"2", output=new, overwrite=True)
        self.assertEqual(nv.NupFile(new).packages[0].meta.records[nv.TLV_ICON], self.ICON + b"2")

    def test_failed_save_as_keeps_the_file_it_would_overwrite(self) -> None:
        path, new = self.write(build({"f": b"x"}, meta=b"")), self.tmp / "keep.nup"
        new.write_bytes(b"existing")
        cancel = threading.Event()
        cancel.set()
        data = bytes(build({"f": os.urandom(1 << 20)}))
        path = self.write(data)
        with self.assertRaises(nv.Cancelled):
            nv.set_icon(path, self.ICON, output=str(new), overwrite=True, cancel=cancel)
        self.assertEqual(new.read_bytes(), b"existing")

    def assert_untouched(self, path: str, data: bytes) -> None:
        self.assertEqual(Path(path).read_bytes(), data)
        self.assertEqual([p.name for p in self.tmp.iterdir() if "nupedit-" in p.name], [])

    def test_temp_file_name_has_no_leading_dot(self) -> None:
        names = []
        real = nv.tempfile.mkstemp

        def spy(**kwargs):
            names.append(kwargs["prefix"])
            return real(**kwargs)

        with unittest.mock.patch.object(nv.tempfile, "mkstemp", spy):
            nv.set_icon(self.write(build(self.TREE)), self.ICON)
        self.assertFalse(names[0].startswith("."))

    @unittest.skipUnless(os.name == "nt", "Windows file attributes")
    def test_edit_does_not_change_hidden_attribute(self) -> None:
        real_replace = os.replace

        def share_marks_temp_hidden(src, dst):  # what a network share can do to the temp file
            nv._set_windows_attributes(src, nv._ATTRIBUTE_HIDDEN)
            real_replace(src, dst)

        hidden = lambda p: bool(nv._windows_attributes(p) & nv._ATTRIBUTE_HIDDEN)
        path = self.write(build(self.TREE))
        with unittest.mock.patch.object(nv.os, "replace", share_marks_temp_hidden):
            nv.set_icon(path, self.ICON)
            self.assertFalse(hidden(path))  # a visible file stays visible

            new = str(self.tmp / "new.nup")
            nv.set_icon(path, self.ICON, output=new)
            self.assertFalse(hidden(new))  # and so does a new copy

            nv._set_windows_attributes(path, nv._ATTRIBUTE_HIDDEN)
            nv.set_icon(path, self.ICON)
            self.assertTrue(hidden(path))  # a file the user hid stays hidden
        nv._set_windows_attributes(path, None)

    def test_cancel_leaves_original_intact(self) -> None:
        data = bytes(build({"f": os.urandom(9 << 20)}, meta=tlv(self.META)))
        path = self.write(data)
        cancel = threading.Event()
        with self.assertRaises(nv.Cancelled):
            nv.set_icon(path, self.ICON, cancel=cancel, progress=lambda *_: cancel.set())
        self.assert_untouched(path, data)

    def test_metadata_stored_before_file_data(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META), meta_before_blobs=True))
        before = self.contents(path)
        original = nv.NupFile(path)
        self.assertLess(original.packages[0].meta_offset, original.blob_offset)  # fixture is right
        nv.set_icon(path, self.ICON)
        nup = nv.NupFile(path)
        self.assertEqual(nup.packages[0].meta.records, {**self.META, nv.TLV_ICON: self.ICON})
        self.assertEqual(self.contents(path), before)
        self.assertEqual(self.extract_all(nup).failures, [])  # per-file SHA-256 still passes

        size = os.path.getsize(path)  # a second edit reuses the block added at the end
        nv.set_icon(path, self.ICON[:-8])
        self.assertEqual(os.path.getsize(path), size - 8)
        self.assertEqual(self.contents(path), before)

    def test_metadata_sharing_bytes_with_a_file(self) -> None:
        block = tlv(self.META)  # stored as a raw file too, so this offset holds valid metadata
        data = build({"f": block}, meta=block)
        toc_size = struct.unpack_from("<Q", data, 0x10)[0]
        blob = struct.unpack_from("<Q", data, 0x38)[0]
        toc = bytearray(data[0x80:0x80 + toc_size])
        struct.pack_into("<Q", toc, 0x30 + 0x20, blob)
        data[0x80:0x80 + toc_size] = toc
        data[0x18:0x38] = hashlib.sha256(toc).digest()
        path = self.write(bytes(data))
        nv.set_icon(path, self.ICON)
        self.assertEqual(self.contents(path), {"f": block})
        self.assertEqual(nv.NupFile(path).packages[0].meta.records[nv.TLV_ICON], self.ICON)

    def test_refuses_corrupt_metadata(self) -> None:
        bad = struct.pack("<HHI", nv.TLV_TITLE_NAME, 0, 9999) + b"short"
        data = bytes(build(self.TREE, meta=bad))
        path = self.write(data)
        with self.assertRaisesRegex(nv.NupError, "overruns"):
            nv.set_icon(path, self.ICON)
        self.assert_untouched(path, data)

    @unittest.skipUnless(os.name == "nt", "Windows locks open files")
    def test_file_in_use_gives_clear_error_and_keeps_original(self) -> None:
        data = bytes(build(self.TREE, meta=tlv(self.META)))
        path = self.write(data)
        with open(path, "rb"), unittest.mock.patch.object(nv.time, "sleep"):
            with self.assertRaisesRegex(nv.NupError, "Close the emulator"):
                nv.set_icon(path, self.ICON)
        self.assert_untouched(path, data)

    def test_prepare_icon_without_pillow(self) -> None:
        png, txt = self.tmp / "a.png", self.tmp / "a.txt"
        png.write_bytes(b"\x89PNG\r\n\x1a\nrest")
        txt.write_bytes(b"not an image")
        with unittest.mock.patch.dict(sys.modules, {"PIL": None}):
            self.assertEqual(nv.prepare_icon(str(png))[0], png.read_bytes())
            with self.assertRaisesRegex(nv.NupError, "JPEG or PNG"):
                nv.prepare_icon(str(txt))

    def test_prepare_icon_with_pillow(self) -> None:
        try:
            from PIL import Image
        except ImportError:
            self.skipTest("Pillow not installed")
        src = self.tmp / "wide.png"
        Image.new("RGBA", (640, 360), (10, 20, 30, 128)).save(src)
        data, note = nv.prepare_icon(str(src))
        result = Image.open(io.BytesIO(data))
        self.assertEqual((result.format, result.size), ("JPEG", (256, 256)))
        self.assertIn("converted", note)
        ready = self.tmp / "ready.jpg"
        ready.write_bytes(data)
        self.assertEqual(nv.prepare_icon(str(ready))[0], data)  # no needless re-encoding
        junk = self.tmp / "junk.png"
        junk.write_bytes(b"not an image")
        with self.assertRaisesRegex(nv.NupError, "could not read"):
            nv.prepare_icon(str(junk))


class EditMetadata(Base):
    META = SetIcon.META
    TREE = SetIcon.TREE

    def edit(self, path: str, **fields) -> nv.NupFile:
        nv.edit_metadata(path, {0: nv.MetadataChange(**fields)})
        return nv.NupFile(path)

    def test_changes_fields_and_keeps_the_rest(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        meta = self.edit(path, title="新しい Title", publisher="Dev", display_version="9.9.9").packages[0].meta
        self.assertEqual(meta.records, {**self.META, nv.TLV_TITLE_NAME: "新しい Title".encode(),
                                        nv.TLV_PUBLISHER: b"Dev", nv.TLV_DISPLAY_VERSION: b"9.9.9"})

    def test_untouched_fields_stay_and_empty_removes(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        meta = self.edit(path, title="").packages[0].meta
        self.assertNotIn(nv.TLV_TITLE_NAME, meta.records)
        self.assertEqual(meta.text(nv.TLV_DISPLAY_VERSION), "1.2.3")
        self.assertEqual(meta.records[nv.TLV_ICON], self.META[nv.TLV_ICON])

    def test_localized_titles(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        self.assertEqual(self.edit(path, localized_titles={"JA": "ゲーム", "en-us": "Game"}).packages[0].meta.titles,
                         {"ja": "ゲーム", "en-us": "Game"})
        self.assertEqual(self.edit(path, localized_titles={}).packages[0].meta.titles, {})
        with self.assertRaisesRegex(nv.NupError, "language tag"):
            self.edit(path, localized_titles={"not a tag": "x"})

    def test_off_by_one_ids_are_kept(self) -> None:
        shifted = {t - 1 if t < 0x100 else t: v for t, v in self.META.items()}
        path = self.write(build(self.TREE, meta=tlv(shifted)))
        nup = self.edit(path, title="Renamed", publisher="Dev")
        self.assertEqual(nup.packages[0].meta.records,
                         {**self.META, nv.TLV_TITLE_NAME: b"Renamed", nv.TLV_PUBLISHER: b"Dev"})

    def test_new_block_on_a_package_with_no_metadata(self) -> None:
        path = self.write(build(self.TREE))
        meta = self.edit(path, title="Hello").packages[0].meta
        self.assertEqual(meta.text(nv.TLV_TITLE_NAME), "Hello")

    def test_metadata_before_file_data_can_be_edited_repeatedly(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META), meta_before_blobs=True))
        self.edit(path, title="One")
        size = os.path.getsize(path)
        nup = self.edit(path, title="Two")
        self.assertEqual(os.path.getsize(path), size)
        self.assertEqual(nup.packages[0].meta.text(nv.TLV_TITLE_NAME), "Two")
        self.assertEqual(self.extract_all(nup).failures, [])

    def test_bad_values_leave_the_file_untouched(self) -> None:
        data = bytes(build(self.TREE, meta=tlv(self.META)))
        path = self.write(data)
        for fields, message in (({"title": "x" * 600}, "too long"), ({"display_version": "1" * 20}, "too long"),
                                ({"publisher": "bad\x07"}, "control characters")):
            with self.subTest(fields=fields), self.assertRaisesRegex(nv.NupError, message):
                self.edit(path, **fields)
        self.assertEqual(Path(path).read_bytes(), data)
        with self.assertRaisesRegex(nv.NupError, "nothing to change"):
            nv.edit_metadata(path, {})

    def test_targets_follow_what_emulators_read(self) -> None:
        def pkg(index, kind, version):
            return nv.Package(index, 1, 0, nv.NO_DIR, nv.NO_DIR, version, kind, 0, 0, 0)

        class Fake:
            packages = [pkg(0, 1, 0x10000), pkg(1, 0, 0), pkg(2, 1, 0x20000), pkg(3, 2, 0)]

        self.assertEqual(nv.app_target(Fake).kind, 0)
        self.assertEqual(nv.version_target(Fake).version, 0x20000)
        Fake.packages = [pkg(0, 0, 0), pkg(1, 2, 0)]
        self.assertEqual(nv.version_target(Fake).kind, 0)

    def test_command_line(self) -> None:
        path = self.write(build(self.TREE, meta=tlv(self.META)))
        self.assertEqual(nv.main(["edit", path, "--title", "CLI", "--developer", "Studio", "--version", "2.0",
                                  "--lang-title", "ja=ゲーム"]), 0)
        meta = nv.NupFile(path).packages[0].meta
        self.assertEqual((meta.text(nv.TLV_TITLE_NAME), meta.text(nv.TLV_PUBLISHER),
                          meta.text(nv.TLV_DISPLAY_VERSION), meta.titles),
                         ("CLI", "Studio", "2.0", {"ja": "ゲーム"}))
        self.assertEqual(nv.main(["edit", path, "--lang-title", "ja="]), 0)
        self.assertEqual(nv.NupFile(path).packages[0].meta.titles, {})
        self.assertEqual(nv.main(["edit", path]), 2)


class Cli(Base):
    def test_extract_and_exit_codes(self) -> None:
        path = self.write(build({"romfs": {"a": b"1", "b": b"2"}}))
        self.assertEqual(nv.main(["extract", path, str(self.out), "-p", "0",
                                  "--path", "romfs/a"]), 0)
        self.assertEqual([p.name for p in self.out.iterdir()], ["a"])
        self.assertEqual(nv.main(["extract", path, str(self.out), "--path", "missing"]), 2)
        self.assertEqual(nv.main(["info", self.write(b"junk", "junk.nup")]), 2)


if __name__ == "__main__":
    unittest.main()
