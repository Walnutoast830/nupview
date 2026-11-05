#!/usr/bin/env python3
"""nupview - browse and extract .nup (NX Package) containers.

    python nupview.py [game.nup]                       open the GUI
    python nupview.py info game.nup                    packages and metadata
    python nupview.py ls game.nup [-p PACKAGE]         list every file
    python nupview.py extract game.nup OUT [-p PACKAGE] [--path romfs/x] [--overwrite]
    python nupview.py set-icon game.nup IMAGE [-p PACKAGE] [-o new.nup]
    python nupview.py edit game.nup [--title T] [--developer D] [--version V] [--lang-title ja=T]

Implements the reader side of SPEC.md v1 from https://github.com/a55uka/nup.
Needs Python 3.10+. Zstandard support comes from the standard library on
Python 3.14+, otherwise from `pip install zstandard`. Pillow is optional: it
adds JPEG previews and converts new icons to the 256x256 JPEG consoles use.

File names inside a container are untrusted: they never reach the filesystem
without going through safe_component().
"""

from __future__ import annotations

import argparse
import codecs
import errno
import hashlib
import io
import os
import re
import shutil
import struct
import sys
import tempfile
import threading
import time
import unicodedata
from dataclasses import dataclass, field
from typing import BinaryIO, Callable, Iterator, NamedTuple

try:
    import tkinter as tk
    from tkinter import filedialog, font as tkfont, messagebox, ttk
except ImportError:  # CLI still works on Python builds without Tk
    tk = None

# ---------------------------------------------------------------------------
# Format (SPEC.md)
# ---------------------------------------------------------------------------

_SUPER = struct.Struct("<4sHHQQ32sQQII16s32s")
_TOC_HEAD = struct.Struct("<4sIQQQQQ")
_PKG = struct.Struct("<QIIIIBBHIQI20x")
_DIR = struct.Struct("<IIIIQ")
_FILE = struct.Struct("<IIQQQ32sBBH12x")
_TLV = struct.Struct("<HHI")

HEADER_SIZE = 0x80
NO_DIR = 0xFFFFFFFF
EXTENT_ALIGN = 16
CHUNK_SIZE = 1 << 20
MAX_META_SIZE = 64 << 20

CODEC_RAW, CODEC_ZSTD = 0, 1
CODEC_NAMES = {CODEC_RAW: "raw", CODEC_ZSTD: "zstd"}
KIND_NAMES = ("base", "update", "addon", "addon_update", "system")
FLAG_STANDALONE_UPDATE = 0x01

TLV_NPDM = 0x01
TLV_NACP = 0x02
TLV_ICON = 0x03
TLV_DISPLAY_VERSION = 0x04
TLV_TITLE_NAME = 0x05
TLV_PUBLISHER = 0x06
TLV_BUILD_ID = 0x07
TLV_SOURCE_DUMP = 0x08
TLV_LOCALIZED_TITLES = 0x09
TLV_LOCALIZED_ICONS = 0x0A


class NupError(Exception):
    """Malformed or unreadable NUP data."""


class Cancelled(Exception):
    """The user stopped an extraction."""


def _zstd_backend() -> tuple[Callable[[BinaryIO], BinaryIO], tuple[type[BaseException], ...]]:
    """Return (open a decompressing reader over a stream, its error types)."""
    try:
        from compression import zstd
    except ImportError:
        pass
    else:
        return (lambda raw: zstd.ZstdFile(raw, "rb")), (zstd.ZstdError, EOFError)
    try:
        import zstandard
    except ImportError:
        raise NupError("this file needs zstd: use Python 3.14+ or run "
                       "'pip install zstandard'") from None
    return (lambda raw: zstandard.ZstdDecompressor().stream_reader(raw)), (zstandard.ZstdError,)


class FileEntry(NamedTuple):
    name: str
    size: int
    extent_offset: int
    extent_size: int
    sha256: bytes
    codec: int


@dataclass
class Meta:
    """Package metadata, always keyed by the type IDs from the spec."""
    records: dict[int, bytes] = field(default_factory=dict)
    titles: dict[str, str] = field(default_factory=dict)
    icons: dict[str, bytes] = field(default_factory=dict)
    problem: str = ""

    def text(self, tlv: int) -> str:
        return self.records.get(tlv, b"").decode("utf-8", "replace")


@dataclass
class Package:
    index: int
    title_id: int
    root_dir: int
    exefs_dir: int
    romfs_dir: int
    version: int
    kind: int
    flags: int
    meta_offset: int
    meta_size: int
    meta: Meta = field(default_factory=Meta)
    layout: tuple[str, ...] = ()  # where "extract all" puts this package

    @property
    def kind_name(self) -> str:
        return KIND_NAMES[self.kind]

    @property
    def version_label(self) -> str:
        display = self.meta.text(TLV_DISPLAY_VERSION)
        if display:
            return display
        if self.version == 0:
            return "no version"
        # Switch 2 stores a revision counter in steps of 0x10000 (see upstream cli.py).
        if self.version & 0xFFFF == 0:
            return f"revision {self.version >> 16}"
        return f"{self.version >> 16}.{(self.version >> 8) & 0xFF}.{self.version & 0xFF}"

    @property
    def label(self) -> str:
        title = self.meta.text(TLV_TITLE_NAME)
        parts = [self.kind_name, f"{self.title_id:016X}", self.version_label]
        return " · ".join(parts + ([title] if title else []))


def _looks_like_text(data: bytes) -> bool:
    try:
        decoded = data.decode("utf-8")
    except UnicodeDecodeError:
        return False
    return not any(ord(c) < 0x20 and c not in "\t\r\n" for c in decoded)


def _uses_shifted_ids(records: dict[int, bytes]) -> bool:
    """Detect blocks written with upstream's off-by-one metadata type IDs.

    Upstream commit 1d904e1 made every ID one lower than the spec (NPDM 0, ...
    source dump 7). Such tools always write a source dump, so ID 7 holds text
    where a spec-conformant file would have a 32-byte binary build ID.
    """
    if 0 in records:  # 0 is unassigned in the spec; shifted files put the NPDM here
        return True
    candidate = records.get(7)
    return candidate is not None and (len(candidate) != 32 or _looks_like_text(candidate))


def _parse_localized(payload: bytes) -> dict[str, bytes]:
    out: dict[str, bytes] = {}
    pos = 0
    while pos < len(payload):
        lang_len = payload[pos]
        pos += 1
        lang = payload[pos:pos + lang_len].decode("ascii", "replace").lower()
        pos += lang_len
        if pos + 4 > len(payload):
            raise NupError("localized record truncated")
        (data_len,) = struct.unpack_from("<I", payload, pos)
        pos += 4
        if pos + data_len > len(payload):
            raise NupError("localized record overruns its block")
        out[lang] = payload[pos:pos + data_len]
        pos += data_len
    return out


def parse_meta(block: bytes) -> Meta:
    """Decode a meta block. Bad metadata is reported, never fatal: the files still extract."""
    meta = Meta()
    try:
        pos = 0
        while pos + _TLV.size <= len(block):
            tlv, _reserved, size = _TLV.unpack_from(block, pos)
            pos += _TLV.size
            if pos + size > len(block):
                raise NupError("metadata record overruns its block")
            meta.records.setdefault(tlv, block[pos:pos + size])
            pos += size
        if _uses_shifted_ids(meta.records):
            meta.records = {(t + 1 if t < TLV_LOCALIZED_ICONS else t): v
                            for t, v in meta.records.items()}
        if TLV_LOCALIZED_TITLES in meta.records:
            meta.titles = {k: v.decode("utf-8", "replace") for k, v in
                           _parse_localized(meta.records[TLV_LOCALIZED_TITLES]).items()}
        if TLV_LOCALIZED_ICONS in meta.records:
            meta.icons = _parse_localized(meta.records[TLV_LOCALIZED_ICONS])
    except NupError as exc:
        meta.problem = str(exc)
    return meta


class _ExtentReader(io.RawIOBase):
    """Read-only view of one extent of a file."""

    def __init__(self, fh: BinaryIO, offset: int, size: int) -> None:
        super().__init__()
        self._fh = fh
        self._left = size
        fh.seek(offset)

    def readable(self) -> bool:
        return True

    def readinto(self, buffer) -> int:
        want = min(len(buffer), self._left)
        if want == 0:
            return 0
        data = self._fh.read(want)
        if not data:
            raise NupError("file ended in the middle of an extent")
        buffer[:len(data)] = data
        self._left -= len(data)
        return len(data)


class NupFile:
    """A validated .nup container. Holds no open handle, so the file is never locked."""

    def __init__(self, path: str) -> None:
        self.path = os.path.abspath(path)
        with open(self.path, "rb") as fh:
            actual_size = os.fstat(fh.fileno()).st_size
            head = fh.read(HEADER_SIZE)
            if len(head) < HEADER_SIZE:
                raise NupError("not a NUP file: too short")
            (magic, header_size, self.header_version, toc_offset, toc_size, toc_sha,
             self.blob_offset, self.file_size, package_count, flags, self.uuid,
             _reserved) = _SUPER.unpack(head)
            if magic[:3] != b"NUP":
                raise NupError("not a NUP file: bad magic")
            if magic[3] != 1:
                raise NupError(f"unsupported NUP major version {magic[3]}")
            if header_size < HEADER_SIZE or toc_offset != header_size:
                raise NupError("bad header or TOC offset")
            if flags:
                raise NupError(f"unknown container flags {flags:#x}")
            if self.file_size != actual_size:
                raise NupError(f"size mismatch: header says {self.file_size:,} bytes, file is "
                               f"{actual_size:,} (truncated or incomplete download?)")
            if (self.blob_offset < toc_offset + toc_size or self.blob_offset % EXTENT_ALIGN
                    or self.blob_offset > self.file_size or package_count < 1):
                raise NupError("inconsistent layout in header")
            fh.seek(toc_offset)
            toc = fh.read(toc_size)
            if hashlib.sha256(toc).digest() != toc_sha:
                raise NupError("TOC checksum mismatch: file is corrupt")
            self.toc_offset, self.toc_size = toc_offset, toc_size
            self._parse_toc(toc, package_count)
            self._load_metadata(fh)
        self._assign_layout()

    def _parse_toc(self, toc: bytes, package_count: int) -> None:
        if len(toc) < _TOC_HEAD.size:
            raise NupError("TOC truncated")
        magic, count, self.dir_count, self.file_count, pool_off, pool_size, _ = \
            _TOC_HEAD.unpack_from(toc, 0)
        if magic != b"TOC\x01" or count != package_count:
            raise NupError("bad TOC header")
        self._toc = toc
        self._dirs_off = _TOC_HEAD.size + count * _PKG.size
        self._files_off = self._dirs_off + self.dir_count * _DIR.size
        self._children_off = self._files_off + self.file_count * _FILE.size
        if self._children_off > len(toc):
            raise NupError("TOC truncated")
        if pool_off < self._children_off or pool_off + pool_size > len(toc):
            raise NupError("string pool out of bounds")
        self._pool_off, self._pool_size = pool_off, pool_size

        slots = 0
        for name_off, name_len, _first, child_count, _ in _DIR.iter_unpack(
                toc[self._dirs_off:self._files_off]):
            self._check_name(name_off, name_len)
            slots += child_count
        self._slot_count = slots
        if self._children_off + slots * 4 > len(toc):
            raise NupError("children array out of bounds")
        for _name_off, _name_len, first, child_count, _ in _DIR.iter_unpack(
                toc[self._dirs_off:self._files_off]):
            if first + child_count > slots:
                raise NupError("directory child range out of bounds")

        node_total = self.dir_count + self.file_count
        if slots and max(struct.unpack_from(f"<{slots}I", toc, self._children_off)) >= node_total:
            raise NupError("directory entry points at a node that does not exist")

        for name_off, name_len, size, offset, stored, _sha, codec, _flags, _ in _FILE.iter_unpack(
                toc[self._files_off:self._children_off]):
            self._check_name(name_off, name_len)
            if codec not in CODEC_NAMES:
                raise NupError(f"unknown codec {codec}")
            if size and (offset < self.blob_offset or offset % EXTENT_ALIGN
                         or offset + stored > self.file_size):
                raise NupError("file extent out of bounds")

        self.packages: list[Package] = []
        for i in range(count):
            title_id, root, exefs, romfs, version, kind, pkg_flags, _r, _r2, meta_off, meta_size = \
                _PKG.unpack_from(toc, _TOC_HEAD.size + i * _PKG.size)
            if kind >= len(KIND_NAMES):
                raise NupError(f"unknown package kind {kind}")
            if root >= self.dir_count or any(d != NO_DIR and d >= self.dir_count
                                             for d in (exefs, romfs)):
                raise NupError(f"package {i}: directory index out of bounds")
            if meta_size and meta_off + meta_size > self.file_size:
                raise NupError(f"package {i}: metadata out of bounds")
            self.packages.append(Package(i, title_id, root, exefs, romfs, version, kind,
                                         pkg_flags, meta_off, meta_size))

    def _check_name(self, offset: int, length: int) -> None:
        if offset + length > self._pool_size:
            raise NupError("name out of string pool bounds")

    def _name(self, offset: int, length: int) -> str:
        start = self._pool_off + offset
        return self._toc[start:start + length].decode("utf-8", "replace")

    def _load_metadata(self, fh: BinaryIO) -> None:
        for pkg in self.packages:
            if not pkg.meta_size:
                continue
            if pkg.meta_size > MAX_META_SIZE:
                pkg.meta = Meta(problem="metadata block too large, ignored")
                continue
            fh.seek(pkg.meta_offset)
            pkg.meta = parse_meta(fh.read(pkg.meta_size))

    def _assign_layout(self) -> None:
        """Mirror the directory layout `nup pack` reads, so extractions can be re-packed."""
        dlc_counts: dict[int, int] = {}
        used: set[tuple[str, ...]] = set()
        for pkg in self.packages:
            tid = f"{pkg.title_id:016x}"
            if pkg.kind == 0:
                layout = ("base",)
            elif pkg.kind == 1:
                layout = ("updates", str(pkg.version))
            elif pkg.kind == 2:
                n = dlc_counts.get(pkg.title_id, 0)
                dlc_counts[pkg.title_id] = n + 1
                layout = ("dlc", tid, str(n))
            else:
                layout = (pkg.kind_name, tid, str(pkg.version))
            if layout in used:
                layout = layout[:-1] + (f"{layout[-1]}-{pkg.index}",)
            used.add(layout)
            pkg.layout = layout

    # ---- tree access ----

    def dir_name(self, index: int) -> str:
        name_off, name_len, _first, _count, _ = _DIR.unpack_from(
            self._toc, self._dirs_off + index * _DIR.size)
        return self._name(name_off, name_len)

    def dir_child_count(self, index: int) -> int:
        return _DIR.unpack_from(self._toc, self._dirs_off + index * _DIR.size)[3]

    def file(self, index: int) -> FileEntry:
        name_off, name_len, size, offset, stored, sha, codec, _flags, _ = _FILE.unpack_from(
            self._toc, self._files_off + index * _FILE.size)
        return FileEntry(self._name(name_off, name_len), size, offset, stored, sha, codec)

    def children(self, dir_index: int) -> list[tuple[bool, int, str]]:
        """List a directory as (is_dir, index, name)."""
        _off, _len, first, count, _ = _DIR.unpack_from(
            self._toc, self._dirs_off + dir_index * _DIR.size)
        out = []
        for node in struct.unpack_from(f"<{count}I", self._toc, self._children_off + first * 4):
            if node < self.dir_count:
                out.append((True, node, self.dir_name(node)))
            else:
                index = node - self.dir_count
                out.append((False, index, self.file(index).name))
        return out

    def walk(self, dir_index: int, prefix: tuple[str, ...] = ()
             ) -> Iterator[tuple[tuple[str, ...], bool, int]]:
        """Yield (path parts, is_dir, index) depth-first. Cycles raise NupError."""
        seen = {dir_index}
        stack = [(prefix, iter(self.children(dir_index)))]
        while stack:
            parts, entries = stack[-1]
            entry = next(entries, None)
            if entry is None:
                stack.pop()
                continue
            is_dir, index, name = entry
            path = parts + (name,)
            yield path, is_dir, index
            if is_dir:
                if index in seen:
                    raise NupError(f"directory loop at {'/'.join(path)}")
                seen.add(index)
                stack.append((path, iter(self.children(index))))

    def resolve(self, pkg: Package, relpath: str) -> tuple[bool, int] | None:
        """Find a '/'-separated path under a package: (is_dir, index) or None."""
        current = (True, pkg.root_dir)
        for part in filter(None, relpath.replace("\\", "/").split("/")):
            if not current[0]:
                return None
            for is_dir, index, name in self.children(current[1]):
                if name == part:
                    current = (is_dir, index)
                    break
            else:
                return None
        return current

    # ---- content ----

    def iter_content(self, entry: FileEntry, fh: BinaryIO, limit: int | None = None
                     ) -> Iterator[bytes]:
        """Stream a file's uncompressed bytes, stopping early at `limit` if given."""
        if entry.size == 0:
            return
        raw = _ExtentReader(fh, entry.extent_offset, entry.extent_size)
        errors: tuple[type[BaseException], ...] = ()
        if entry.codec == CODEC_RAW:
            if entry.extent_size != entry.size:
                raise NupError(f"{entry.name}: raw extent size differs from file size")
            stream: BinaryIO = raw  # type: ignore[assignment]
        else:
            opener, errors = _zstd_backend()
            stream = opener(raw)  # type: ignore[arg-type]
        produced = 0
        try:
            while True:
                want = CHUNK_SIZE if limit is None else min(CHUNK_SIZE, limit - produced)
                if want == 0:
                    return
                data = stream.read(want)
                if not data:
                    break
                produced += len(data)
                if produced > entry.size:
                    raise NupError(f"{entry.name}: content is larger than recorded size")
                yield data
        except errors as exc:
            raise NupError(f"{entry.name}: decompression failed: {exc}") from exc
        finally:
            stream.close()
        if produced != entry.size:
            raise NupError(f"{entry.name}: expected {entry.size} bytes, got {produced}")

    def read_head(self, entry: FileEntry, limit: int) -> bytes:
        with open(self.path, "rb") as fh:
            return b"".join(self.iter_content(entry, fh, limit))


# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------

_WINDOWS_RESERVED = {"CON", "PRN", "AUX", "NUL",
                     *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}


def safe_component(name: str) -> str:
    """Turn a container name into one safe path component, or raise ValueError.

    Separators and dot-names are refused outright since no real dump has them
    and they are how a crafted file would escape the output folder. Characters
    that are merely invalid on Windows (which includes ':' for alternate data
    streams) are replaced.
    """
    if name in ("", ".", "..") or any(c in name for c in "/\\\0"):
        raise ValueError(f"unsafe file name {name!r}")
    if os.name != "nt":
        return name
    clean = re.sub(r'[<>:"|?*\x00-\x1f]', "_", name).rstrip(" .") or "_"
    if clean.split(".")[0].upper() in _WINDOWS_RESERVED:
        clean = "_" + clean
    return clean


def _fs(path: str) -> str:
    """Let Windows handle paths over 260 characters; dumps can nest deeply."""
    if os.name != "nt" or path.startswith("\\\\?\\"):
        return path
    return "\\\\?\\UNC\\" + path[2:] if path.startswith("\\\\") else "\\\\?\\" + path


@dataclass
class Target:
    """Something to extract: a directory's contents, or one file, placed at `parts`."""
    is_dir: bool
    index: int
    parts: tuple[str, ...] = ()


@dataclass
class Plan:
    dest: str
    files: list[tuple[str, int]] = field(default_factory=list)
    dirs: list[str] = field(default_factory=list)
    failures: list[tuple[str, str]] = field(default_factory=list)
    renamed: int = 0
    total_bytes: int = 0

    def count_existing(self) -> int:
        return sum(os.path.lexists(_fs(path)) for path, _ in self.files)


@dataclass
class Result:
    written: int = 0
    skipped: int = 0
    bytes_written: int = 0
    renamed: int = 0
    cancelled: bool = False
    failures: list[tuple[str, str]] = field(default_factory=list)


def build_plan(nup: NupFile, dest: str, targets: list[Target]) -> Plan:
    """Map targets to output paths, refusing unsafe names and colliding paths."""
    dest = os.path.abspath(dest)
    plan = Plan(dest)
    claimed: dict[str, int] = {}  # NTFS is case-insensitive, RomFS is not

    def out_path(parts: tuple[str, ...]) -> str | None:
        try:
            safe = [safe_component(p) for p in parts]
        except ValueError as exc:
            plan.failures.append(("/".join(parts), str(exc)))
            return None
        if safe != list(parts):
            plan.renamed += 1
        return os.path.join(dest, *safe)

    def add_file(parts: tuple[str, ...], index: int) -> None:
        path = out_path(parts)
        if path is None:
            return
        key = path.casefold() if os.name == "nt" else path
        if key in claimed:
            if claimed[key] != index:
                plan.failures.append(("/".join(parts), "another file already uses this path"))
            return
        claimed[key] = index
        plan.files.append((path, index))
        plan.total_bytes += nup.file(index).size

    for target in targets:
        if not target.is_dir:
            add_file(target.parts or (nup.file(target.index).name,), target.index)
            continue
        root = out_path(target.parts) if target.parts else dest
        if root is None:
            continue  # the folder's own name is unsafe, already recorded as a failure
        plan.dirs.append(root)
        for parts, is_dir, index in nup.walk(target.index, target.parts):
            if is_dir:
                path = out_path(parts)
                if path:
                    plan.dirs.append(path)
            else:
                add_file(parts, index)
    return plan


def _extract_one(nup: NupFile, fh: BinaryIO, entry: FileEntry, path: str, verify: bool,
                 cancel: threading.Event | None, on_bytes: Callable[[int], None]) -> None:
    temp = path + ".nupart"
    digest = hashlib.sha256()
    try:
        with open(_fs(temp), "wb") as out:
            for chunk in nup.iter_content(entry, fh):
                if cancel is not None and cancel.is_set():
                    raise Cancelled
                out.write(chunk)
                if verify:
                    digest.update(chunk)
                on_bytes(len(chunk))
        if verify and digest.digest() != entry.sha256:
            raise NupError("SHA-256 mismatch: stored data is corrupt")
        os.replace(_fs(temp), _fs(path))
    finally:
        if os.path.lexists(_fs(temp)):
            os.unlink(_fs(temp))


def run_plan(nup: NupFile, plan: Plan, *, overwrite: bool = False, verify: bool = True,
             cancel: threading.Event | None = None,
             progress: Callable[[int, int, str], None] | None = None) -> Result:
    """Write a plan to disk. One bad file is recorded and the rest still extract."""
    result = Result(renamed=plan.renamed, failures=list(plan.failures))
    done = 0

    def on_bytes(n: int) -> None:
        nonlocal done
        done += n
        result.bytes_written += n
        if progress:
            progress(done, result.written + result.skipped, current)

    current = ""
    for path in plan.dirs:
        try:
            os.makedirs(_fs(path), exist_ok=True)
        except OSError as exc:
            result.failures.append((path, str(exc)))
    with open(nup.path, "rb") as fh:
        for path, index in plan.files:
            if cancel is not None and cancel.is_set():
                result.cancelled = True
                break
            entry = nup.file(index)
            current = os.path.relpath(path, plan.dest)
            if not overwrite and os.path.lexists(_fs(path)):
                result.skipped += 1
                done += entry.size
                continue
            written_before, done_before = result.bytes_written, done
            try:
                os.makedirs(_fs(os.path.dirname(path)), exist_ok=True)
                _extract_one(nup, fh, entry, path, verify, cancel, on_bytes)
                result.written += 1
            except Cancelled:
                result.bytes_written = written_before
                result.cancelled = True
                break
            except (NupError, OSError) as exc:
                result.bytes_written = written_before
                done = done_before + entry.size  # keep the progress bar's total reachable
                result.failures.append((current, str(exc)))
                if isinstance(exc, OSError) and exc.errno == errno.ENOSPC:
                    break
            if progress:
                progress(done, result.written + result.skipped, current)
    return result


# ---------------------------------------------------------------------------
# Editing
# ---------------------------------------------------------------------------

ICON_DIMENSION = 256
MAX_ICON_INPUT = 64 << 20


def prepare_icon(path: str) -> tuple[bytes, str]:
    """Load an image for use as an icon: returns (stored bytes, what was done to it).

    With Pillow, anything it can read becomes the 256x256 JPEG the spec describes,
    centre-cropped if not square. Without it only JPEG and PNG are accepted, unchanged.
    """
    with open(path, "rb") as fh:
        data = fh.read(MAX_ICON_INPUT + 1)
    if len(data) > MAX_ICON_INPUT:
        raise NupError("that image is too large to use as an icon")
    try:
        from PIL import Image, ImageOps
    except ImportError:
        if image_kind(data) not in ("JPEG", "PNG"):
            raise NupError("icon must be a JPEG or PNG (install Pillow for other formats)") from None
        return data, "stored unchanged; install Pillow to convert it to a 256x256 JPEG"
    try:
        image = Image.open(io.BytesIO(data))
        size = (ICON_DIMENSION, ICON_DIMENSION)
        if image.format == "JPEG" and image.size == size and image.mode == "RGB":
            image.load()  # catches a truncated file before it is stored
            return data, "already a 256x256 JPEG, stored unchanged"
        original = f"{image.format} {image.width}x{image.height}"
        image = ImageOps.exif_transpose(image).convert("RGBA")
        flat = Image.new("RGB", image.size, (255, 255, 255))
        flat.paste(image, mask=image.getchannel("A"))
        output = io.BytesIO()
        ImageOps.fit(flat, size, Image.LANCZOS).save(output, "JPEG", quality=95)
    except (OSError, ValueError, Image.DecompressionBombError) as exc:
        raise NupError(f"could not read that image: {exc}") from exc
    return output.getvalue(), f"converted from {original} to a 256x256 JPEG"


MAX_TITLE_BYTES, MAX_PUBLISHER_BYTES, MAX_VERSION_BYTES = 0x1FF, 0xFF, 0xF  # NACP field sizes


@dataclass
class MetadataChange:
    """One package's edits. None leaves a field alone; an empty value removes it."""
    title: str | None = None
    publisher: str | None = None
    display_version: str | None = None
    localized_titles: dict[str, str] | None = None  # replaces the whole set
    icon: bytes | None = None


@dataclass
class EditResult:
    path: str
    package: Package
    removed_localized: int


def app_target(nup: NupFile, selector: str | None = None) -> Package:
    """Where the title, developer and icon belong: the base, else whichever package already
    holds them, else the first (SPEC 5.1). Emulators read these from the base."""
    if selector is not None:
        return _select_packages(nup, selector)[0]
    base = next((p for p in nup.packages if p.kind == 0), None)
    if base is not None:
        return base
    app = (TLV_TITLE_NAME, TLV_PUBLISHER, TLV_DISPLAY_VERSION, TLV_ICON,
           TLV_LOCALIZED_TITLES, TLV_LOCALIZED_ICONS)
    return next((p for p in nup.packages if any(t in p.meta.records for t in app)), nup.packages[0])


def version_target(nup: NupFile, selector: str | None = None) -> Package:
    """Where the display version belongs: emulators show the newest update's, else the base's."""
    if selector is not None:
        return _select_packages(nup, selector)[0]
    updates = [p for p in nup.packages if p.kind == 1]
    return max(updates, key=lambda p: p.version) if updates else app_target(nup)


_ATTRIBUTE_HIDDEN, _ATTRIBUTE_SYSTEM, _ATTRIBUTE_ARCHIVE = 0x2, 0x4, 0x20
_ATTRIBUTE_NOT_INDEXED = 0x2000
_KEPT_ATTRIBUTES = (_ATTRIBUTE_HIDDEN | _ATTRIBUTE_SYSTEM | _ATTRIBUTE_ARCHIVE
                    | _ATTRIBUTE_NOT_INDEXED)


def _windows_attributes(path: str) -> int | None:
    if os.name != "nt":
        return None
    import ctypes
    get = ctypes.WinDLL("kernel32", use_last_error=True).GetFileAttributesW
    get.argtypes, get.restype = [ctypes.c_wchar_p], ctypes.c_uint32
    value = get(path)
    return None if value == 0xFFFFFFFF else value


def _set_windows_attributes(path: str, original: int | None) -> None:
    """Give an edited file the original's attributes; a new file gets ordinary ones.

    Cosmetic only, so a failure here is ignored: the edit itself has already succeeded.
    """
    if os.name != "nt":
        return
    import ctypes
    wanted = _ATTRIBUTE_ARCHIVE if original is None else original & _KEPT_ATTRIBUTES
    set_attributes = ctypes.WinDLL("kernel32", use_last_error=True).SetFileAttributesW
    set_attributes.argtypes, set_attributes.restype = [ctypes.c_wchar_p, ctypes.c_uint32], ctypes.c_int
    set_attributes(path, wanted or 0x80)  # 0x80 is FILE_ATTRIBUTE_NORMAL


def _split_tlvs(block: bytes) -> list[tuple[int, bytes]]:
    out, pos = [], 0
    while pos + _TLV.size <= len(block):
        tlv, _reserved, size = _TLV.unpack_from(block, pos)
        pos += _TLV.size
        if pos + size > len(block):
            raise NupError("metadata record overruns its block")
        out.append((tlv, block[pos:pos + size]))
        pos += size
    return out


def _normalize_text(value: str, label: str, limit: int) -> str:
    """Clean a metadata string. "" is allowed and means remove the field."""
    text = unicodedata.normalize("NFC", value).strip()
    if any(unicodedata.category(c) == "Cc" for c in text):
        raise NupError(f"{label} can't contain control characters")
    if len(text.encode("utf-8")) > limit:
        raise NupError(f"{label} is too long: consoles allow {limit} bytes")
    return text


def _encode_localized(entries: dict[str, str]) -> bytes:
    out = bytearray()
    for lang, title in sorted(entries.items()):
        tag = lang.strip().lower()
        if not re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", tag) or len(tag) > 255:
            raise NupError(f"{lang!r} isn't a valid language tag (examples: ja, en-us, zh-hans)")
        data = _normalize_text(title, f"The {tag} title", MAX_TITLE_BYTES).encode("utf-8")
        out += bytes([len(tag)]) + tag.encode("ascii") + struct.pack("<I", len(data)) + data
    return bytes(out)


def _apply_change(own: list[tuple[int, bytes]], change: MetadataChange) -> tuple[bytes, set[int]]:
    """Return the new block and the spec IDs it may have changed."""
    # Keep whichever type IDs this block already uses (see _uses_shifted_ids). The reader
    # decides per block, and an empty block reads as spec IDs, so that is what it gets.
    shifted = _uses_shifted_ids(dict(reversed(own))) if own else False
    new: dict[int, bytes | None] = {}
    for tlv, value, label, limit in ((TLV_TITLE_NAME, change.title, "The title", MAX_TITLE_BYTES),
                                     (TLV_PUBLISHER, change.publisher, "The developer", MAX_PUBLISHER_BYTES),
                                     (TLV_DISPLAY_VERSION, change.display_version, "The version", MAX_VERSION_BYTES)):
        if value is not None:
            new[tlv] = _normalize_text(value, label, limit).encode("utf-8") or None
    if change.localized_titles is not None:
        new[TLV_LOCALIZED_TITLES] = _encode_localized(change.localized_titles) or None
    if change.icon is not None:
        new[TLV_ICON] = change.icon
        new[TLV_LOCALIZED_ICONS] = None
    stored = {tlv - shifted: value for tlv, value in new.items()}
    records = [r for r in own if r[0] not in stored]
    records += [(tlv, value) for tlv, value in stored.items() if value is not None]
    records.sort(key=lambda r: r[0])
    block = b"".join(_TLV.pack(t, 0, len(v)) + v for t, v in records)
    if len(block) > MAX_META_SIZE:
        raise NupError("the metadata would be too large")
    return block, set(new)


def edit_metadata(path: str, changes: dict[int, MetadataChange], *, output: str | None = None,
                  overwrite: bool = False, cancel: threading.Event | None = None,
                  progress: Callable[[int, int], None] | None = None) -> EditResult:
    """Change metadata on the given packages, by writing a complete new file and swapping it in.

    The original is untouched until the new file has been written and validated, so a
    crash, a full disk or a cancel leaves it intact. Anything not being changed, including
    every other package's metadata, is kept byte for byte.
    """
    if not changes:
        raise NupError("there is nothing to change")
    source = os.path.abspath(path)
    destination = os.path.abspath(output) if output else source
    in_place = os.path.normcase(destination) == os.path.normcase(source)
    if output and not in_place and not overwrite and os.path.exists(destination):
        raise NupError(f"{destination} already exists")
    nup = NupFile(source)
    for index in changes:
        if nup.packages[index].meta.problem:
            raise NupError(f"can't edit this package's metadata: {nup.packages[index].meta.problem}")

    extents_end = nup.blob_offset
    for index in range(nup.file_count):
        entry = nup.file(index)
        if entry.size:
            extents_end = max(extents_end, entry.extent_offset + entry.extent_size)
    used = [p for p in nup.packages if p.meta_size]
    meta_start = min((p.meta_offset for p in used), default=nup.file_size)
    if any(p.meta_size > MAX_META_SIZE for p in used):
        raise NupError("this file's metadata is too large to edit safely")

    with open(source, "rb") as fh:
        blocks = []
        for pkg in nup.packages:
            fh.seek(pkg.meta_offset)
            blocks.append(fh.read(pkg.meta_size) if pkg.meta_size else b"")
        fh.seek(0)
        head = bytearray(fh.read(nup.toc_offset))

    touched: dict[int, set[int]] = {}
    for index, change in changes.items():
        blocks[index], touched[index] = _apply_change(_split_tlvs(blocks[index]), change)

    toc = bytearray(nup._toc)

    def point_at(pkg: Package, offset: int, size: int) -> None:
        struct.pack_into("<QI", toc, _TOC_HEAD.size + pkg.index * _PKG.size + 0x20, offset, size)

    if meta_start >= extents_end:
        # Every block sits after the file data, as `nup pack` writes them: rebuild that tail.
        copy_end, tail = meta_start, b"".join(blocks)
        cursor = meta_start
        for pkg, block in zip(nup.packages, blocks):
            point_at(pkg, cursor if block else 0, len(block))
            cursor += len(block)
    else:
        # Other packers put blocks before the file data. Those bytes must stay where they are,
        # so add new blocks at the end, reusing the space if an earlier edit already did.
        edited = [p for p in used if p.index in changes]
        kept_end = max((p.meta_offset + p.meta_size for p in used if p.index not in changes), default=0)
        first = min((p.meta_offset for p in edited), default=nup.file_size)
        at_end = (len(edited) == len(changes) and first >= max(extents_end, kept_end)
                  and sum(p.meta_size for p in edited) == nup.file_size - first)
        copy_end = first if at_end else nup.file_size
        cursor, tail = copy_end, b""
        for index in sorted(changes):
            block = blocks[index]
            point_at(nup.packages[index], cursor if block else 0, len(block))
            tail += block
            cursor += len(block)
    head[0x18:0x38] = hashlib.sha256(toc).digest()
    head[0x40:0x48] = struct.pack("<Q", cursor)

    directory = os.path.dirname(destination)
    if shutil.disk_usage(directory).free < cursor + (1 << 20):
        raise NupError(f"not enough free space: this needs {human_size(cursor)} free in "
                       f"{directory} while it writes the new file")
    before = os.stat(source)
    # No leading dot: network shares can mark dot-files hidden, and the mark survives the rename.
    handle, temp = tempfile.mkstemp(prefix="nupedit-", suffix=".tmp", dir=directory)
    try:
        with os.fdopen(handle, "wb") as out, open(source, "rb") as src:
            out.write(head)
            out.write(toc)
            position = nup.toc_offset + nup.toc_size
            src.seek(position)
            while position < copy_end:
                if cancel is not None and cancel.is_set():
                    raise Cancelled
                chunk = src.read(min(4 << 20, copy_end - position))
                if not chunk:
                    raise NupError("file ended while copying it")
                out.write(chunk)
                position += len(chunk)
                if progress:
                    progress(position, copy_end)
            out.write(tail)
            out.flush()
            os.fsync(out.fileno())

        check = NupFile(temp)

        def summary(n: NupFile) -> tuple:
            """Everything that must survive: the whole file tree, plus all untouched metadata."""
            return (n._toc[n._dirs_off:],
                    [(p.title_id, p.version, p.kind,
                      {t: v for t, v in p.meta.records.items() if t not in touched.get(p.index, ())})
                     for p in n.packages])

        if summary(check) != summary(nup) or any(
                check.packages[i].meta.records != parse_meta(blocks[i]).records for i in changes):
            raise NupError("the new file failed validation, so the original was kept")
        now = os.stat(source)
        if (now.st_size, now.st_mtime_ns) != (before.st_size, before.st_mtime_ns):
            raise NupError("the file changed while it was being edited, so nothing was replaced")
        shutil.copymode(source, temp)
        attributes = _windows_attributes(source) if in_place else None
        for attempt in range(5):  # antivirus and indexers briefly hold files on Windows
            try:
                os.replace(temp, destination)
                break
            except PermissionError:
                if attempt == 4:
                    raise NupError("couldn't replace the file because something has it open. "
                                   "Close the emulator and try again; the original is unchanged") from None
                time.sleep(0.25 * (attempt + 1))
        _set_windows_attributes(destination, attributes)
    finally:
        if os.path.exists(temp):
            os.unlink(temp)
    removed = sum(len(nup.packages[i].meta.icons) for i, c in changes.items() if c.icon is not None)
    return EditResult(destination, nup.packages[min(changes)], removed)


def set_icon(path: str, icon: bytes, *, package: str | None = None, output: str | None = None,
             overwrite: bool = False, cancel: threading.Event | None = None,
             progress: Callable[[int, int], None] | None = None) -> EditResult:
    """Replace a package's icon. Language-specific icons are removed from that package,
    because consoles prefer them over the default and would hide the new icon."""
    target = app_target(NupFile(path), package)
    return edit_metadata(path, {target.index: MetadataChange(icon=icon)}, output=output,
                         overwrite=overwrite, cancel=cancel, progress=progress)


def human_size(n: int) -> str:
    value = float(n)
    for unit in ("B", "KB", "MB", "GB"):
        if value < 1024:
            return f"{int(value)} B" if unit == "B" else f"{value:.1f} {unit}"
        value /= 1024
    return f"{value:.2f} TB"


def package_stats(nup: NupFile, pkg: Package) -> tuple[int, int]:
    files = size = 0
    for _parts, is_dir, index in nup.walk(pkg.root_dir):
        if not is_dir:
            files += 1
            size += nup.file(index).size
    return files, size


def summarize(result: Result) -> str:
    text = f"{result.written:,} files extracted ({human_size(result.bytes_written)})"
    if result.skipped:
        text += f", {result.skipped:,} already existed and were skipped"
    if result.failures:
        text += f", {len(result.failures):,} failed"
    if result.cancelled:
        text += ", cancelled before finishing"
    return text


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------

def _select_packages(nup: NupFile, selector: str | None) -> list[Package]:
    if selector is None:
        return list(nup.packages)
    if selector.isdigit():
        if int(selector) >= len(nup.packages):
            raise NupError(f"no package with index {selector}")
        return [nup.packages[int(selector)]]
    matches = [p for p in nup.packages if p.kind_name == selector]
    if not matches:
        raise NupError(f"no package matching {selector!r}")
    return matches


def _cmd_info(args: argparse.Namespace) -> int:
    nup = NupFile(args.file)
    print(f"file:     {nup.path}")
    print(f"size:     {human_size(nup.file_size)} ({nup.file_size:,} bytes)")
    print(f"contents: {len(nup.packages)} packages, {nup.dir_count:,} dirs, "
          f"{nup.file_count:,} files")
    for pkg in nup.packages:
        files, size = package_stats(nup, pkg)
        print(f"\n[{pkg.index}] {pkg.label}")
        print(f"    {files:,} file{'' if files == 1 else 's'}, {human_size(size)}")
        meta = pkg.meta
        if meta.text(TLV_PUBLISHER):
            print(f"    publisher:  {meta.text(TLV_PUBLISHER)}")
        for lang, title in sorted(meta.titles.items()):
            print(f"    title[{lang}]: {title}")
        if TLV_BUILD_ID in meta.records:
            print(f"    build id:   {meta.records[TLV_BUILD_ID].rstrip(bytes(1)).hex().upper()}")
        if meta.text(TLV_SOURCE_DUMP):
            print(f"    source:     {meta.text(TLV_SOURCE_DUMP)}")
        if pkg.flags & FLAG_STANDALONE_UPDATE:
            print("    standalone update (needs a matching base elsewhere)")
        if meta.problem:
            print(f"    metadata problem: {meta.problem}")
    return 0


def _cmd_ls(args: argparse.Namespace) -> int:
    nup = NupFile(args.file)
    for pkg in _select_packages(nup, args.package):
        for parts, is_dir, index in nup.walk(pkg.root_dir):
            if is_dir:
                continue
            entry = nup.file(index)
            codec = CODEC_NAMES[entry.codec] if entry.size else "empty"
            print(f"[{pkg.index}] {entry.size:>13,}  {codec:<5}  {'/'.join(parts)}")
    return 0


def _cmd_extract(args: argparse.Namespace) -> int:
    nup = NupFile(args.file)
    packages = _select_packages(nup, args.package)
    single = len(packages) == 1 and args.package is not None
    targets: list[Target] = []
    for pkg in packages:
        prefix = () if single else pkg.layout
        if not args.path:
            targets.append(Target(True, pkg.root_dir, prefix))
            continue
        for wanted in args.path:
            found = nup.resolve(pkg, wanted)
            if found is None:
                continue
            base = wanted.replace("\\", "/").rstrip("/").rsplit("/", 1)[-1]
            targets.append(Target(found[0], found[1], prefix + ((base,) if base else ())))
    if not targets:
        raise NupError("none of the given paths exist in the selected packages")

    plan = build_plan(nup, args.dest, targets)
    show_progress = sys.stderr.isatty()

    def progress(done: int, _files: int, _current: str) -> None:
        pct = done * 100 // plan.total_bytes if plan.total_bytes else 100
        sys.stderr.write(f"\r{pct:3d}%  {human_size(done)} / {human_size(plan.total_bytes)}   ")

    result = run_plan(nup, plan, overwrite=args.overwrite, verify=not args.no_verify,
                      progress=progress if show_progress else None)
    if show_progress:
        sys.stderr.write("\n")
    print(f"{summarize(result)} -> {plan.dest}")
    if result.renamed:
        print(f"{result.renamed:,} names were adjusted to be valid on this system")
    for name, reason in result.failures:
        print(f"  failed: {name}: {reason}", file=sys.stderr)
    return 1 if result.failures else 0


def _cmd_set_icon(args: argparse.Namespace) -> int:
    icon, note = prepare_icon(args.image)
    show = sys.stderr.isatty()

    def progress(done: int, total: int) -> None:
        sys.stderr.write(f"\rwriting new file: {done * 100 // max(total, 1):3d}%")

    result = set_icon(args.file, icon, package=args.package, output=args.output,
                      progress=progress if show else None)
    if show:
        sys.stderr.write("\n")
    print(f"icon set on {result.package.kind_name} package ({note}) -> {result.path}")
    if result.removed_localized:
        print(f"removed {result.removed_localized} localized icons so the new one is shown")
    return 0


def _cmd_edit(args: argparse.Namespace) -> int:
    nup = NupFile(args.file)
    changes: dict[int, MetadataChange] = {}
    app, version = app_target(nup, args.package), version_target(nup, args.package)
    if args.title is not None:
        changes.setdefault(app.index, MetadataChange()).title = args.title
    if args.developer is not None:
        changes.setdefault(app.index, MetadataChange()).publisher = args.developer
    if args.version is not None:
        changes.setdefault(version.index, MetadataChange()).display_version = args.version
    if args.lang_title:
        titles = dict(app.meta.titles)
        for item in args.lang_title:
            lang, separator, value = item.partition("=")
            if not separator:
                raise NupError(f"--lang-title expects LANG=TITLE, got {item!r}")
            titles.pop(lang.strip().lower(), None)
            if value.strip():
                titles[lang.strip().lower()] = value
        changes.setdefault(app.index, MetadataChange()).localized_titles = titles
    if not changes:
        raise NupError("nothing to change: give at least one of --title, --developer, "
                       "--version or --lang-title")
    show = sys.stderr.isatty()

    def progress(done: int, total: int) -> None:
        sys.stderr.write(f"\rwriting new file: {done * 100 // max(total, 1):3d}%")

    result = edit_metadata(args.file, changes, output=args.output, progress=progress if show else None)
    if show:
        sys.stderr.write("\n")
    edited = ", ".join(nup.packages[i].kind_name for i in sorted(changes))
    print(f"metadata saved on the {edited} package{'s' if len(changes) > 1 else ''} -> {result.path}")
    return 0


# ---------------------------------------------------------------------------
# GUI
# ---------------------------------------------------------------------------

PREVIEW_TEXT_BYTES = 64 << 10
PREVIEW_HEX_BYTES = 16 << 10
PREVIEW_IMAGE_MAX = 16 << 20
MAX_SEARCH_RESULTS = 2000
ICON_SIZE = 192


def hex_dump(data: bytes) -> str:
    lines = []
    for pos in range(0, len(data), 16):
        row = data[pos:pos + 16]
        left = " ".join(f"{b:02x}" for b in row[:8])
        right = " ".join(f"{b:02x}" for b in row[8:])
        text = "".join(chr(b) if 32 <= b < 127 else "." for b in row)
        lines.append(f"{pos:08x}  {left:<23}  {right:<23}  {text}")
    return "\n".join(lines)


def decode_preview(data: bytes) -> str | None:
    """Return text if the bytes look like text, else None."""
    if data[:2] in (b"\xff\xfe", b"\xfe\xff"):
        return data.decode("utf-16", "replace")
    # Incremental decoding tolerates the preview cutting a character in half at the end.
    try:
        text = codecs.getincrementaldecoder("utf-8")().decode(data)
    except UnicodeDecodeError:
        return None
    if any(ord(c) < 0x20 and c not in "\t\r\n\f" for c in text):
        return None
    return text.replace("\r\n", "\n")


def image_kind(data: bytes) -> str | None:
    if data[:4] == b"\x89PNG":
        return "PNG"
    if data[:2] == b"\xff\xd8":
        return "JPEG"
    if data[:4] == b"GIF8":
        return "GIF"
    return None


def make_photo(data: bytes, max_size: int):
    """Build a Tk image. Returns (photo or None, description)."""
    kind = image_kind(data) or "image"
    try:
        from PIL import Image, ImageTk
    except ImportError:
        if kind == "JPEG":
            return None, "JPEG image (run 'pip install pillow' to preview it)"
        photo = tk.PhotoImage(data=data)
        description = f"{kind} image, {photo.width()}×{photo.height()}"
        shrink = max(photo.width(), photo.height()) // max_size + 1
        return (photo.subsample(shrink) if shrink > 1 else photo), description
    image = Image.open(io.BytesIO(data))
    description = f"{kind} image, {image.width}×{image.height}"
    image.thumbnail((max_size, max_size))
    return ImageTk.PhotoImage(image), description


@dataclass
class Node:
    kind: str  # "package", "dir" or "file"
    index: int
    pkg: Package
    parts: tuple[str, ...]  # path from the package root


class App:
    def __init__(self, path: str | None = None) -> None:
        if os.name == "nt":
            try:
                import ctypes
                ctypes.windll.shcore.SetProcessDpiAwareness(1)
            except (AttributeError, OSError):
                pass
        self.root = tk.Tk()
        self.root.title("NUP Viewer")
        self.root.geometry("1120x700")
        self.nup: NupFile | None = None
        self.nodes: dict[str, Node] = {}
        self.stats: dict[int, tuple[int, int]] = {}
        self.top_items: list[str] = []
        self.search_items: list[str] = []
        self.search_index: list[tuple[str, Package, int, tuple[str, ...]]] | None = None
        self.photo = None
        self.after_ids: dict[str, str] = {}
        self.worker: threading.Thread | None = None
        self.cancel = threading.Event()
        self.closing = False
        self.progress_state: tuple[int, int, str] = (0, 0, "")
        self.job_plan: Plan | None = None
        self.job_result: Result | None = None
        self.job_error: str = ""
        self._build_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        if path:
            self.root.after(50, lambda: self.open_path(path))

    def _build_ui(self) -> None:
        root = self.root
        style = ttk.Style(root)
        if os.name == "nt" and "vista" in style.theme_names():
            style.theme_use("vista")
        line = tkfont.nametofont("TkDefaultFont").metrics("linespace")
        style.configure("Treeview", rowheight=line + 6)

        bar = ttk.Frame(root, padding=(8, 8, 8, 4))
        bar.pack(fill="x")
        self.open_btn = ttk.Button(bar, text="Open…", command=self.choose_file)
        self.open_btn.pack(side="left")
        self.extract_sel_btn = ttk.Button(bar, text="Extract selected…", state="disabled",
                                          command=self.extract_selected)
        self.extract_sel_btn.pack(side="left", padx=(8, 0))
        self.extract_all_btn = ttk.Button(bar, text="Extract all…", state="disabled",
                                          command=self.extract_all)
        self.extract_all_btn.pack(side="left", padx=(8, 0))
        self.icon_btn = ttk.Button(bar, text="Change icon…", state="disabled",
                                   command=self.change_icon)
        self.icon_btn.pack(side="left", padx=(8, 0))
        self.metadata_btn = ttk.Button(bar, text="Edit metadata…", state="disabled",
                                       command=self.edit_metadata_dialog)
        self.metadata_btn.pack(side="left", padx=(8, 0))
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self._debounce("search", 250, self.run_search))
        self.search_entry = ttk.Entry(bar, textvariable=self.search_var, width=32, state="disabled")
        self.search_entry.pack(side="right")
        ttk.Label(bar, text="Find file:").pack(side="right", padx=(0, 6))

        status = ttk.Frame(root, padding=(8, 4, 8, 8))
        status.pack(side="bottom", fill="x")
        self.status_var = tk.StringVar(value="Open a .nup file to get started.")
        ttk.Label(status, textvariable=self.status_var, anchor="w").pack(
            side="left", fill="x", expand=True)
        self.cancel_btn = ttk.Button(status, text="Cancel", command=self.cancel.set)
        self.progress = ttk.Progressbar(status, length=220, maximum=1000)

        panes = ttk.PanedWindow(root, orient="horizontal")
        panes.pack(fill="both", expand=True, padx=8)

        left = ttk.Frame(panes)
        self.tree = ttk.Treeview(left, columns=("size", "stored", "codec"), selectmode="extended")
        self.tree.heading("#0", text="Name", anchor="w")
        self.tree.heading("size", text="Size", anchor="e")
        self.tree.heading("stored", text="Stored", anchor="e")
        self.tree.heading("codec", text="Codec", anchor="w")
        # Only the name column stretches, and it starts narrow: a pane narrower than the
        # requested widths would otherwise clip the columns on the right.
        scale = root.winfo_fpixels("1i") / 96
        self.tree.column("#0", width=int(200 * scale), minwidth=int(120 * scale), stretch=True)
        self.tree.column("size", width=int(80 * scale), anchor="e", stretch=False)
        self.tree.column("stored", width=int(80 * scale), anchor="e", stretch=False)
        self.tree.column("codec", width=int(55 * scale), stretch=False)
        scroll = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=scroll.set)
        self.tree.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        panes.add(left, weight=3)

        right = ttk.Frame(panes, padding=(8, 0, 0, 0))
        mono = ("Consolas", 9) if os.name == "nt" else "TkFixedFont"
        self.details = tk.Text(right, height=11, wrap="word", state="disabled", relief="flat",
                               background=root.cget("background"), font="TkDefaultFont",
                               padx=4, pady=4)
        self.details.pack(fill="x")
        self.image_label = ttk.Label(right, anchor="center")
        preview_frame = ttk.Frame(right)
        preview_frame.pack(side="bottom", fill="both", expand=True, pady=(6, 0))
        self.preview = tk.Text(preview_frame, wrap="none", state="disabled", font=mono)
        pv = ttk.Scrollbar(preview_frame, orient="vertical", command=self.preview.yview)
        ph = ttk.Scrollbar(preview_frame, orient="horizontal", command=self.preview.xview)
        self.preview.configure(yscrollcommand=pv.set, xscrollcommand=ph.set)
        pv.pack(side="right", fill="y")
        ph.pack(side="bottom", fill="x")
        self.preview.pack(side="left", fill="both", expand=True)
        panes.add(right, weight=2)

        def place_divider(event) -> None:  # the real width is unknown until first layout
            if event.width > 1:
                panes.unbind("<Configure>")
                panes.sashpos(0, int(event.width * 0.58))
        panes.bind("<Configure>", place_divider)

        self.menu = tk.Menu(root, tearoff=False)
        self.menu.add_command(label="Extract…", command=self.extract_selected)

        self.tree.bind("<<TreeviewOpen>>", self.on_open_node)
        self.tree.bind("<<TreeviewSelect>>", lambda _e: self._debounce("select", 100, self.show_selection))
        self.tree.bind("<Button-3>", self.on_right_click)
        root.bind("<Control-o>", lambda _e: self.choose_file())

    # ---- helpers ----

    def _debounce(self, key: str, delay: int, fn: Callable[[], None]) -> None:
        if key in self.after_ids:
            self.root.after_cancel(self.after_ids[key])
        self.after_ids[key] = self.root.after(delay, fn)

    @staticmethod
    def _set_text(widget: tk.Text, text: str) -> None:
        widget.configure(state="normal")
        widget.delete("1.0", "end")
        widget.insert("1.0", text)
        widget.configure(state="disabled")

    def _set_image(self, photo) -> None:
        self.photo = photo  # Tk drops images with no Python reference
        if photo is None:
            self.image_label.configure(image="")
            self.image_label.pack_forget()
        else:
            self.image_label.configure(image=photo)
            self.image_label.pack(after=self.details, pady=(4, 0))

    # ---- opening ----

    def choose_file(self) -> None:
        if self.worker is not None:
            return
        path = filedialog.askopenfilename(
            title="Open NUP file", filetypes=[("NUP containers", "*.nup"), ("All files", "*.*")])
        if path:
            self.open_path(path)

    def open_path(self, path: str) -> None:
        self.root.configure(cursor="watch")
        self.root.update_idletasks()
        try:
            nup = NupFile(path)
            stats = {pkg.index: package_stats(nup, pkg) for pkg in nup.packages}
        except (NupError, OSError) as exc:
            messagebox.showerror("Could not open file", f"{path}\n\n{exc}")
            return
        finally:
            self.root.configure(cursor="")
        self.nup, self.stats = nup, stats
        self.nodes.clear()
        self.search_index = None
        self.search_items = []
        self.tree.delete(*self.tree.get_children())
        self.top_items = []
        self.search_var.set("")
        for pkg in nup.packages:
            files, size = stats[pkg.index]
            iid = self.tree.insert("", "end", text=pkg.label, open=False,
                                   values=(human_size(size), "", ""))
            self.nodes[iid] = Node("package", pkg.root_dir, pkg, ())
            self.top_items.append(iid)
            if nup.dir_child_count(pkg.root_dir):
                self.tree.insert(iid, "end", text="")
        self.root.title(f"{os.path.basename(path)} - NUP Viewer")
        self.extract_all_btn.configure(state="normal")
        self.icon_btn.configure(state="normal")
        self.metadata_btn.configure(state="normal")
        self.search_entry.configure(state="normal")
        self._set_status_summary()
        if self.top_items:
            self.tree.selection_set(self.top_items[0])
            self.tree.focus(self.top_items[0])
            self.tree.item(self.top_items[0], open=True)
            self._populate(self.top_items[0])

    def _set_status_summary(self) -> None:
        nup = self.nup
        count = len(nup.packages)
        self.status_var.set(f"{os.path.basename(nup.path)}  ·  {human_size(nup.file_size)}  ·  "
                            f"{count} package{'s' if count != 1 else ''}  ·  "
                            f"{nup.file_count:,} files")

    # ---- tree ----

    def _populate(self, iid: str) -> None:
        kids = self.tree.get_children(iid)
        node = self.nodes[iid]
        if len(kids) != 1 or kids[0] in self.nodes:
            return
        self.tree.delete(kids[0])
        children = sorted(self.nup.children(node.index), key=lambda c: (not c[0], c[2].casefold()))
        for is_dir, index, name in children:
            parts = node.parts + (name,)
            if is_dir:
                count = self.nup.dir_child_count(index)
                child = self.tree.insert(iid, "end", text=f"{name}/",
                                         values=(f"{count:,} items", "", ""))
                self.nodes[child] = Node("dir", index, node.pkg, parts)
                if count:
                    self.tree.insert(child, "end", text="")
            else:
                entry = self.nup.file(index)
                child = self.tree.insert(iid, "end", text=name, values=self._file_values(entry))
                self.nodes[child] = Node("file", index, node.pkg, parts)

    @staticmethod
    def _file_values(entry: FileEntry) -> tuple[str, str, str]:
        if not entry.size:
            return ("0 B", "0 B", "empty")
        return (human_size(entry.size), human_size(entry.extent_size), CODEC_NAMES[entry.codec])

    def on_open_node(self, _event) -> None:
        iid = self.tree.focus()
        if iid in self.nodes:
            self._populate(iid)

    def on_right_click(self, event) -> None:
        iid = self.tree.identify_row(event.y)
        if not iid or iid not in self.nodes:
            return
        if iid not in self.tree.selection():
            self.tree.selection_set(iid)
        self.menu.tk_popup(event.x_root, event.y_root)

    # ---- search ----

    def run_search(self) -> None:
        if self.nup is None:
            return
        query = self.search_var.get().strip().casefold()
        if self.search_items:
            self.tree.delete(*self.search_items)
            for iid in self.search_items:
                self.nodes.pop(iid, None)
            self.search_items = []
        if not query:
            for position, iid in enumerate(self.top_items):
                self.tree.reattach(iid, "", position)
            self._set_status_summary()
            return
        if self.search_index is None:
            self.search_index = []
            for pkg in self.nup.packages:
                for parts, is_dir, index in self.nup.walk(pkg.root_dir):
                    if not is_dir:
                        self.search_index.append(("/".join(parts).casefold(), pkg, index, parts))
        for iid in self.top_items:
            self.tree.detach(iid)
        total = 0
        for lowered, pkg, index, parts in self.search_index:
            if query not in lowered:
                continue
            total += 1
            if total > MAX_SEARCH_RESULTS:
                continue
            entry = self.nup.file(index)
            iid = self.tree.insert("", "end", text=f"[{pkg.kind_name}] {'/'.join(parts)}",
                                   values=self._file_values(entry))
            self.nodes[iid] = Node("file", index, pkg, parts)
            self.search_items.append(iid)
        shown = f" (showing first {MAX_SEARCH_RESULTS:,})" if total > MAX_SEARCH_RESULTS else ""
        self.status_var.set(f"{total:,} matching files{shown}")

    # ---- details ----

    def show_selection(self) -> None:
        selection = [i for i in self.tree.selection() if i in self.nodes]
        self.extract_sel_btn.configure(
            state="normal" if selection and self.worker is None else "disabled")
        self._set_image(None)
        self._set_text(self.preview, "")
        if not selection:
            self._set_text(self.details, "")
            return
        if len(selection) > 1:
            self._set_text(self.details, f"{len(selection)} items selected")
            return
        node = self.nodes[selection[0]]
        if node.kind == "package":
            self._show_package(node.pkg)
        elif node.kind == "dir":
            count = self.nup.dir_child_count(node.index)
            self._set_text(self.details, f"Folder: {'/'.join(node.parts)}\n"
                                         f"Package: {node.pkg.kind_name}\n"
                                         f"Contains: {count:,} items")
        else:
            self._show_file(node)

    def _show_package(self, pkg: Package) -> None:
        meta = pkg.meta
        files, size = self.stats[pkg.index]
        lines = [f"Type: {pkg.kind_name}", f"Title ID: {pkg.title_id:016X}",
                 f"Version: {pkg.version_label}  (raw {pkg.version:#x})",
                 f"Contents: {files:,} files, {human_size(size)}"]
        if meta.text(TLV_TITLE_NAME):
            lines.insert(0, f"Title: {meta.text(TLV_TITLE_NAME)}")
        if meta.text(TLV_PUBLISHER):
            lines.append(f"Publisher: {meta.text(TLV_PUBLISHER)}")
        lines += [f"Title [{lang}]: {title}" for lang, title in sorted(meta.titles.items())]
        if TLV_BUILD_ID in meta.records:
            lines.append(f"Build ID: {meta.records[TLV_BUILD_ID].rstrip(bytes(1)).hex().upper()}")
        if meta.text(TLV_SOURCE_DUMP):
            lines.append(f"Source: {meta.text(TLV_SOURCE_DUMP)}")
        if pkg.flags & FLAG_STANDALONE_UPDATE:
            lines.append("Standalone update: needs a matching base elsewhere")
        if meta.problem:
            lines.append(f"Metadata problem: {meta.problem}")
        icon = meta.records.get(TLV_ICON) or next(iter(meta.icons.values()), None)
        if icon:
            try:
                photo, description = make_photo(icon, ICON_SIZE)
                self._set_image(photo)
                lines.append(f"Icon: {description}")
            except (tk.TclError, OSError, ValueError) as exc:
                lines.append(f"Icon: could not be displayed ({exc})")
        self._set_text(self.details, "\n".join(lines))

    def _show_file(self, node: Node) -> None:
        entry = self.nup.file(node.index)
        codec = CODEC_NAMES[entry.codec] if entry.size else "empty"
        lines = [f"File: {'/'.join(node.parts)}", f"Package: {node.pkg.kind_name}",
                 f"Size: {human_size(entry.size)} ({entry.size:,} bytes)"]
        if entry.size:
            ratio = entry.extent_size * 100 / entry.size
            lines.append(f"Stored: {human_size(entry.extent_size)} ({ratio:.0f}%, {codec})")
        lines.append(f"SHA-256: {entry.sha256.hex()}")
        if not entry.size:
            self._set_text(self.details, "\n".join(lines))
            return
        try:
            head = self.nup.read_head(entry, PREVIEW_TEXT_BYTES)
        except (NupError, OSError) as exc:
            self._set_text(self.details, "\n".join(lines))
            self._set_text(self.preview, f"Could not read this file:\n{exc}")
            return
        if image_kind(head) and entry.size <= PREVIEW_IMAGE_MAX:
            try:
                photo, description = make_photo(self.nup.read_head(entry, entry.size), 256)
                self._set_image(photo)
                lines.append(description)
                self._set_text(self.details, "\n".join(lines))
                return
            except (NupError, tk.TclError, OSError, ValueError):
                pass  # not actually an image: fall through to the hex view
        self._set_text(self.details, "\n".join(lines))
        text = decode_preview(head)
        if text is not None:
            note = "" if entry.size <= len(head) else \
                f"\n\n--- first {human_size(len(head))} of {human_size(entry.size)} ---"
            self._set_text(self.preview, text + note)
        else:
            shown = head[:PREVIEW_HEX_BYTES]
            note = "" if entry.size <= len(shown) else \
                f"\n\n--- first {human_size(len(shown))} of {human_size(entry.size)} ---"
            self._set_text(self.preview, hex_dump(shown) + note)

    # ---- extraction ----

    def extract_selected(self) -> None:
        selected = set(self.tree.selection())
        targets = []
        for iid in self.tree.selection():
            node = self.nodes.get(iid)
            if node is None:
                continue
            parent = self.tree.parent(iid)
            covered = False
            while parent:  # a selected ancestor already includes this item
                covered = covered or parent in selected
                parent = self.tree.parent(parent)
            if covered:
                continue
            if node.kind == "package":
                targets.append(Target(True, node.index, node.pkg.layout))
            else:
                targets.append(Target(node.kind == "dir", node.index, node.parts[-1:]))
        if targets:
            self._start_extract(targets)

    def extract_all(self) -> None:
        if self.nup is not None:
            self._start_extract([Target(True, p.root_dir, p.layout) for p in self.nup.packages])

    def _start_extract(self, targets: list[Target]) -> None:
        if self.worker is not None:
            return
        dest = filedialog.askdirectory(title="Extract to folder", mustexist=False)
        if not dest:
            return
        try:
            plan = build_plan(self.nup, dest, targets)
        except NupError as exc:
            messagebox.showerror("Could not extract", str(exc))
            return
        overwrite = False
        existing = plan.count_existing()
        if existing:
            answer = messagebox.askyesnocancel(
                "Files already exist",
                f"{existing:,} of {len(plan.files):,} files already exist in that folder.\n\n"
                "Yes: overwrite them\nNo: keep them and skip those files")
            if answer is None:
                return
            overwrite = answer

        self.cancel.clear()
        self.job_plan, self.job_result, self.job_error = plan, None, ""
        self.progress_state = (0, 0, "")
        self._set_busy(True)
        self.worker = threading.Thread(target=self._work, args=(plan, overwrite), daemon=True)
        self.worker.start()
        self.root.after(100, self._poll)

    def _work(self, plan: Plan, overwrite: bool) -> None:
        def progress(done: int, files: int, current: str) -> None:
            self.progress_state = (done, files, current)
        try:
            self.job_result = run_plan(self.nup, plan, overwrite=overwrite, cancel=self.cancel,
                                       progress=progress)
        except Exception as exc:  # shown to the user; a dead thread would hang the UI
            self.job_error = str(exc)

    def _set_busy(self, busy: bool) -> None:
        state = "disabled" if busy else "normal"
        for widget in (self.open_btn, self.extract_all_btn, self.extract_sel_btn, self.icon_btn,
                       self.metadata_btn):
            widget.configure(state=state)
        if busy:
            self.cancel_btn.pack(side="right", padx=(8, 0))
            self.progress.pack(side="right")
        else:
            self.cancel_btn.pack_forget()
            self.progress.pack_forget()

    def _poll(self) -> None:
        plan = self.job_plan
        done, files, current = self.progress_state
        fraction = done / plan.total_bytes if plan.total_bytes else 1.0
        self.progress.configure(value=min(fraction, 1.0) * 1000)
        self.status_var.set(f"{files:,}/{len(plan.files):,} files · {human_size(done)} of "
                            f"{human_size(plan.total_bytes)} · {current}")
        if self.worker.is_alive():
            self.root.after(100, self._poll)
            return
        self.worker = None
        if self.closing:
            self.root.destroy()
            return
        self._set_busy(False)
        self.show_selection()
        self._finish_extract(plan)

    def _finish_extract(self, plan: Plan) -> None:
        if self.job_error:
            self._set_status_summary()
            messagebox.showerror("Extraction failed", self.job_error)
            return
        result = self.job_result
        summary = summarize(result)
        self.status_var.set(summary)
        if result.renamed:
            summary += f"\n{result.renamed:,} names were adjusted to be valid on this system."
        if result.failures:
            listed = "\n".join(f"• {name}: {reason}" for name, reason in result.failures[:15])
            more = len(result.failures) - 15
            if more > 0:
                listed += f"\n…and {more:,} more"
            messagebox.showwarning("Extraction finished with problems", f"{summary}\n\n{listed}")
        elif result.cancelled:
            messagebox.showinfo("Extraction cancelled", summary)
        elif os.name == "nt":
            if messagebox.askyesno("Extraction complete", f"{summary}\n\nOpen the folder?"):
                os.startfile(plan.dest)
        else:
            messagebox.showinfo("Extraction complete", summary)

    # ---- metadata editing ----

    def change_icon(self) -> None:
        if self.nup is None or self.worker is not None:
            return
        image = filedialog.askopenfilename(
            title="Choose the new icon",
            filetypes=[("Images", "*.jpg *.jpeg *.png *.webp *.bmp *.gif"), ("All files", "*.*")])
        if not image:
            return
        try:
            icon, note = prepare_icon(image)
        except (NupError, OSError) as exc:
            messagebox.showerror("Could not use that image", str(exc))
            return
        source = self.nup.path
        target = app_target(self.nup)
        warning = ""
        if target.meta.icons:
            warning = (f"\n\nThis also removes the {len(target.meta.icons)} language-specific icons, "
                       "which would otherwise be shown instead.")
        answer = messagebox.askyesnocancel(
            "Change icon",
            f"Set the icon on the {target.kind_name} package ({note}).{warning}\n\n"
            f"This writes a full copy of the file first, which needs about "
            f"{human_size(self.nup.file_size)} of free space.\n\n"
            f"Yes: replace {os.path.basename(source)}\nNo: save as a new file")
        if answer is None:
            return
        output = None
        if not answer:
            output = self._ask_save_path(source)
            if not output:
                return
        self._start_edit({target.index: MetadataChange(icon=icon)}, output, "Icon changed")

    @staticmethod
    def _ask_save_path(source: str) -> str:
        return filedialog.asksaveasfilename(
            title="Save new file as", defaultextension=".nup", initialdir=os.path.dirname(source),
            filetypes=[("NUP containers", "*.nup")])

    def edit_metadata_dialog(self) -> None:
        if self.nup is None or self.worker is not None:
            return
        app, version = app_target(self.nup), version_target(self.nup)
        window = tk.Toplevel(self.root)
        window.title("Edit metadata")
        window.transient(self.root)
        window.resizable(False, False)
        frame = ttk.Frame(window, padding=14)
        frame.pack(fill="both", expand=True)
        fields = {"title": tk.StringVar(value=app.meta.text(TLV_TITLE_NAME)),
                  "developer": tk.StringVar(value=app.meta.text(TLV_PUBLISHER)),
                  "version": tk.StringVar(value=version.meta.text(TLV_DISPLAY_VERSION))}
        rows = (("Title", "title", app), ("Developer", "developer", app), ("Version", "version", version))
        for row, (label, key, pkg) in enumerate(rows):
            ttk.Label(frame, text=label).grid(row=row * 2, column=0, sticky="w", padx=(0, 10))
            ttk.Entry(frame, textvariable=fields[key], width=56).grid(row=row * 2, column=1, sticky="ew")
            ttk.Label(frame, text=f"Stored on the {pkg.kind_name} package", foreground="#666666").grid(
                row=row * 2 + 1, column=1, sticky="w", pady=(0, 8))
        ttk.Label(frame, text="Language\ntitles").grid(row=6, column=0, sticky="nw", padx=(0, 10))
        localized = tk.Text(frame, width=56, height=4, font="TkDefaultFont")
        localized.insert("1.0", "\n".join(f"{k}={v}" for k, v in sorted(app.meta.titles.items())))
        localized.grid(row=6, column=1, sticky="ew")
        ttk.Label(frame, text="One per line, for example  ja=ゲーム. These override the title on that language.",
                  foreground="#666666").grid(row=7, column=1, sticky="w", pady=(0, 8))
        ttk.Label(frame, wraplength=460, justify="left",
                  text="A blank field removes that value. Saving writes a full copy of the file first, "
                       f"which needs about {human_size(self.nup.file_size)} of free space.").grid(
            row=8, column=0, columnspan=2, sticky="w", pady=(4, 12))
        self.metadata_window = window

        def submit(new_file: bool) -> None:
            try:
                changes = self.metadata_form_changes(
                    fields["title"].get(), fields["developer"].get(), fields["version"].get(),
                    localized.get("1.0", "end"))
            except NupError as exc:
                messagebox.showerror("Could not save", str(exc), parent=window)
                return
            if not changes:
                messagebox.showinfo("Edit metadata", "Nothing has changed.", parent=window)
                return
            source = self.nup.path
            output = self._ask_save_path(source) if new_file else None
            if new_file and not output:
                return
            window.destroy()
            self._start_edit(changes, output, "Metadata saved")

        buttons = ttk.Frame(frame)
        buttons.grid(row=9, column=0, columnspan=2, sticky="e")
        ttk.Button(buttons, text="Save", command=lambda: submit(False)).pack(side="left")
        ttk.Button(buttons, text="Save as new file…", command=lambda: submit(True)).pack(side="left", padx=8)
        ttk.Button(buttons, text="Cancel", command=window.destroy).pack(side="left")
        window.bind("<Escape>", lambda _e: window.destroy())
        window.grab_set()

    def metadata_form_changes(self, title: str, developer: str, version: str,
                              localized_text: str) -> dict[int, MetadataChange]:
        """Turn the form into changes, leaving out anything that wasn't actually edited."""
        titles: dict[str, str] = {}
        for line in localized_text.splitlines():
            if line.strip():
                lang, separator, value = line.partition("=")
                if not separator or not lang.strip():
                    raise NupError(f"Language titles need the form  lang=title. This line doesn't: {line!r}")
                titles[lang.strip().lower()] = value.strip()
        app, ver = app_target(self.nup), version_target(self.nup)
        changes: dict[int, MetadataChange] = {}

        def add(pkg: Package, **kwargs) -> None:
            changes.setdefault(pkg.index, MetadataChange()).__dict__.update(kwargs)

        if title.strip() != app.meta.text(TLV_TITLE_NAME):
            add(app, title=title)
        if developer.strip() != app.meta.text(TLV_PUBLISHER):
            add(app, publisher=developer)
        if version.strip() != ver.meta.text(TLV_DISPLAY_VERSION):
            add(ver, display_version=version)
        if titles != app.meta.titles:
            add(app, localized_titles=titles)
        return changes

    def _start_edit(self, changes: dict[int, MetadataChange], output: str | None, done: str) -> None:
        source = self.nup.path
        self.cancel.clear()
        self.edit_result, self.job_error = None, ""
        self.edit_done_message = done
        self.edit_progress = (0, 1)
        self._set_busy(True)

        def work() -> None:
            def progress(written: int, total: int) -> None:
                self.edit_progress = (written, total)
            try:
                # The save dialog has already confirmed overwriting an existing file.
                self.edit_result = edit_metadata(source, changes, output=output, overwrite=True,
                                                 cancel=self.cancel, progress=progress)
            except Cancelled:
                pass
            except Exception as exc:  # shown to the user; a dead thread would hang the UI
                self.job_error = str(exc)

        self.worker = threading.Thread(target=work, daemon=True)
        self.worker.start()
        self.root.after(100, self._poll_edit)

    def _poll_edit(self) -> None:
        done, total = self.edit_progress
        self.progress.configure(value=min(done / max(total, 1), 1.0) * 1000)
        self.status_var.set(f"Writing new file: {human_size(done)} of {human_size(total)}")
        if self.worker.is_alive():
            self.root.after(100, self._poll_edit)
            return
        self.worker = None
        if self.closing:
            self.root.destroy()
            return
        self._set_busy(False)
        self.show_selection()
        if self.job_error:
            self._set_status_summary()
            messagebox.showerror("Could not save the change", f"{self.job_error}\n\nYour file was not changed.")
        elif self.edit_result is None:
            self._set_status_summary()
        else:
            result = self.edit_result
            self.open_path(result.path)
            item = self.top_items[result.package.index]
            self.tree.selection_set(item)
            self.tree.focus(item)
            self.show_selection()
            self.status_var.set(f"{self.edit_done_message}: {os.path.basename(result.path)}")

    def on_close(self) -> None:
        if self.worker is None:
            self.root.destroy()
            return
        if messagebox.askyesno("Extraction running", "Cancel the extraction and quit?"):
            self.closing = True
            self.cancel.set()


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(errors="replace")  # game titles may not fit the console codepage

    if not argv or argv[0] not in ("info", "ls", "extract", "set-icon", "edit", "-h", "--help"):
        if len(argv) > 1:
            print("usage: nupview.py [file.nup]  (or: info, ls, extract; see --help)",
                  file=sys.stderr)
            return 2
        if tk is None:
            print("This Python has no tkinter, so the GUI is unavailable. "
                  "Use the info, ls and extract commands.", file=sys.stderr)
            return 2
        App(argv[0] if argv else None).root.mainloop()
        return 0

    parser = argparse.ArgumentParser(prog="nupview", description="View and extract .nup containers. "
                                     "Run with no command to open the GUI.")
    sub = parser.add_subparsers(dest="command", required=True)
    info = sub.add_parser("info", help="show packages and metadata")
    info.add_argument("file")
    info.set_defaults(fn=_cmd_info)
    ls = sub.add_parser("ls", help="list every file")
    ls.add_argument("file")
    ls.add_argument("-p", "--package", help="package index, or base/update/addon")
    ls.set_defaults(fn=_cmd_ls)
    extract = sub.add_parser("extract", help="extract files to a folder")
    extract.add_argument("file")
    extract.add_argument("dest")
    extract.add_argument("-p", "--package", help="package index, or base/update/addon "
                         "(default: all, laid out as base/, updates/<ver>/, dlc/<id>/<n>/)")
    extract.add_argument("--path", action="append", metavar="PATH",
                         help="only this file or folder, e.g. romfs/Data; repeatable")
    extract.add_argument("--overwrite", action="store_true", help="replace existing files")
    extract.add_argument("--no-verify", action="store_true", help="skip SHA-256 checks")
    extract.set_defaults(fn=_cmd_extract)
    seticon = sub.add_parser("set-icon", help="replace a package's icon")
    seticon.add_argument("file")
    seticon.add_argument("image")
    seticon.add_argument("-p", "--package", help="package index, or base/update/addon "
                         "(default: the package holding the game's metadata)")
    seticon.add_argument("-o", "--output", help="write a new file instead of replacing this one")
    seticon.set_defaults(fn=_cmd_set_icon)
    edit = sub.add_parser("edit", help="change the title, developer or version; an empty value removes it")
    edit.add_argument("file")
    edit.add_argument("--title")
    edit.add_argument("--developer")
    edit.add_argument("--version", help="the displayed version, such as 1.2.3")
    edit.add_argument("--lang-title", action="append", metavar="LANG=TITLE",
                      help="language-specific title, repeatable; LANG= removes it")
    edit.add_argument("-p", "--package", help="package index, or base/update/addon (default: title and "
                      "developer go on the base, the version on the newest update)")
    edit.add_argument("-o", "--output", help="write a new file instead of replacing this one")
    edit.set_defaults(fn=_cmd_edit)
    args = parser.parse_args(argv)
    try:
        return args.fn(args)
    except (NupError, OSError) as exc:
        print(f"nupview: error: {exc}", file=sys.stderr)
        return 2
    except KeyboardInterrupt:
        print("\nnupview: interrupted", file=sys.stderr)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
