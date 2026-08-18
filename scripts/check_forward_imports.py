#!/usr/bin/env python3
"""Report imports from a book unit to a later unit in the same book."""

from __future__ import annotations

import argparse
import re
from pathlib import Path


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")
UNIT_RE = re.compile(r"^Unit(\d+)(?:\.lean)?$")


def unit_number(part: str) -> int | None:
    match = UNIT_RE.fullmatch(part)
    return int(match.group(1)) if match else None


def find_forward_imports(books_dir: Path) -> list[tuple[Path, int, int, int, str]]:
    violations = []
    for source in sorted(books_dir.rglob("*.lean")):
        relative = source.relative_to(books_dir)
        if len(relative.parts) < 2:
            continue

        book = relative.parts[0]
        source_unit = unit_number(relative.parts[1])
        if source_unit is None:
            continue

        for line_number, line in enumerate(source.read_text().splitlines(), start=1):
            match = IMPORT_RE.match(line)
            if not match:
                continue

            module = match.group(1)
            parts = module.split(".")
            if len(parts) < 4 or parts[:3] != ["Formalization", "Books", book]:
                continue

            imported_unit = unit_number(parts[3])
            if imported_unit is not None and imported_unit > source_unit:
                violations.append(
                    (relative, line_number, source_unit, imported_unit, module)
                )
    return violations


def main() -> int:
    repository = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "books_dir",
        nargs="?",
        type=Path,
        default=repository / "lean" / "Formalization" / "Books",
        help="Books source directory (default: lean/Formalization/Books)",
    )
    args = parser.parse_args()

    books_dir = args.books_dir.resolve()
    if not books_dir.is_dir():
        parser.error(f"not a directory: {books_dir}")

    violations = find_forward_imports(books_dir)
    for path, line, source_unit, imported_unit, module in violations:
        print(
            f"{path}:{line}: Unit{source_unit:02d} imports later "
            f"Unit{imported_unit:02d}: {module}"
        )

    if violations:
        print(f"Found {len(violations)} within-book forward import(s).")
        return 1

    print("No within-book forward imports found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
