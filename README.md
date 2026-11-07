# nupview

Browse, extract and edit the metadata of [`.nup` (NX Package)](https://github.com/a55uka/nup) containers. A single Python file with a GUI and a command line.

## Requirements

- Python 3.10 or newer, with tkinter for the GUI
- Zstandard support: built in on Python 3.14+, otherwise `pip install zstandard`
- Optional: `pip install pillow` for JPEG previews and for converting new icons to the 256×256 JPEG that consoles use

## GUI

```
python nupview.py [game.nup]
```

- Browse each package's files and metadata, and search by file name
- Preview files as text, an image or hex
- Extract a selection or everything, with a progress bar and cancel
- Change the icon
- Edit the title, developer, version and language-specific titles

## Command line

```
python nupview.py info game.nup
python nupview.py ls game.nup -p base
python nupview.py extract game.nup out_dir
python nupview.py extract game.nup out_dir -p update --path romfs/Data
python nupview.py set-icon game.nup icon.png
python nupview.py set-icon game.nup icon.png -o new.nup
python nupview.py edit game.nup --title "New Title" --developer "Studio" --version 1.2.3
python nupview.py edit game.nup --lang-title ja=ゲーム --lang-title "fr=Le Jeu"
python nupview.py edit game.nup --developer ""
```

`-p` takes a package index or a kind: `base`, `update` or `addon`. In `edit`, an empty value removes a field.

## Repairing a container

Some packers have written a folder's child count as 0 while its entries are still stored. The data is intact but cut off from the folder tree, so tools can't see it. `info` and the GUI warn when files aren't reachable from any package.

```
python nupview.py repair game.nup              # report only, changes nothing
python nupview.py repair game.nup --apply      # fix it; saves game.nup.toc-backup.bin first
python nupview.py repair game.nup --verify     # also check every file's SHA-256
python nupview.py repair game.nup --restore    # undo, from the backup
```

`repair` only fixes unambiguous cases: exactly one empty folder pointing at a run of unused entries that have no other parent, with unique, sorted names. It changes only those counts and the table checksum, and undoes the change if the result isn't better. Anything else is reported but left alone.

Extracting everything recreates the `base/`, `updates/<version>/` and `dlc/<id>/<n>/` layout that `nup pack` reads.

## Behaviour worth knowing

- **Extraction** streams files, so memory use stays low on large containers. Each file's SHA-256 is checked; a corrupt file is reported and removed while the rest carry on.
- **File names are untrusted.** Names that would escape the output folder are refused, and names that aren't valid on Windows are adjusted.
- **Every edit** writes a complete new file, validates it, then swaps it in, so a failure leaves the original intact. It needs free space equal to the container's size on the same drive.
- **Where edits go:** the title, developer and icon go on the base package, and the version on the newest update, because that's where emulators read them. Use `-p` to choose a package yourself.
- **The version** is the displayed one. The numeric version in the package record is part of the package's identity and isn't edited.
- **Language-specific icons** on that package are removed when you change the icon, because consoles prefer them and would hide the new one.
- **Metadata type IDs:** `nup` commit `1d904e1` made its metadata IDs one lower than the spec. nupview reads both variants, and edits keep whichever one the file already uses.

## Tests

```
python -m unittest test_nupview
```

## Notes

This project reads and edits containers you already have. It isn't affiliated with Nintendo and doesn't include any game data or keys.

## License

MIT
