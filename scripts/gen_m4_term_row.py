#!/usr/bin/env python3
"""Render the generated term-routing module from its checked-in template.

The TSV is the row manifest. Validation requires a one-to-one correspondence
between its row keys and the ``eval_<key>_row`` declarations in the template.
"""

import argparse
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
TSV = ROOT / "scripts/m4_term_rows.tsv"
TEMPLATE = ROOT / "scripts/templates/TermRouting.lean"
OUTPUT = ROOT / "Vsa/Sim/rows/TermRouting.lean"
ROW_DECLARATION = re.compile(r"^theorem eval_([A-Za-z0-9_]+)_row\b", re.MULTILINE)


def load_row_keys(tsv: Path) -> list[str]:
    """Read row keys from the tab-separated manifest."""
    keys: list[str] = []
    for line_number, line in enumerate(tsv.read_text().splitlines(), start=1):
        if not line or line.startswith("#") or line.startswith("name\t"):
            continue
        columns = line.split("\t")
        if len(columns) < 6:
            raise ValueError(f"{tsv}:{line_number}: expected at least six columns")
        keys.append(columns[1])
    duplicates = sorted(key for key in set(keys) if keys.count(key) > 1)
    if duplicates:
        raise ValueError(f"duplicate TSV row keys: {', '.join(duplicates)}")
    return keys


def render(tsv: Path = TSV, template: Path = TEMPLATE) -> str:
    """Return the template after checking exact manifest coverage."""
    keys = set(load_row_keys(tsv))
    generated = template.read_text()
    declarations = set(ROW_DECLARATION.findall(generated))
    missing = sorted(keys - declarations)
    extra = sorted(declarations - keys)
    errors: list[str] = []
    if missing:
        errors.append(f"template omits TSV rows: {', '.join(missing)}")
    if extra:
        errors.append(f"template has undeclared rows: {', '.join(extra)}")
    if errors:
        raise ValueError("; ".join(errors))
    return generated


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    try:
        generated = render()
    except ValueError as error:
        print(error, file=sys.stderr)
        return 1
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != generated:
            print(f"{OUTPUT.relative_to(ROOT)} is stale", file=sys.stderr)
            return 1
        print(f"{OUTPUT.relative_to(ROOT)}: up to date")
        return 0
    args.output.write_text(generated)
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
