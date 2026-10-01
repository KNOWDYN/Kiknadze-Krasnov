"""Check source inventory and all documented theorem references (no dependencies)."""
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source_rows = [row for path in sorted((ROOT / "docs/equations").glob("part_*.csv"))
               for row in csv.DictReader(path.open())]
coverage = list(csv.DictReader((ROOT / "docs/coverage.csv").open()))
assert len(source_rows) == 206, "Frozen source inventory changed"
assert {r["item_id"] for r in source_rows} == {r["item_id"] for r in coverage}
assert len({r["item_id"] for r in coverage}) == len(coverage), "Duplicate coverage item"
lean_files = list((ROOT / "KiknadzeKrasnov").glob("*.lean"))
imports = set(re.findall(r"^import KiknadzeKrasnov\.(\w+)$",
                         (ROOT / "KiknadzeKrasnov.lean").read_text(), re.MULTILINE))
assert imports == {path.stem for path in lean_files}, "Root export missing a project module"
symbols = {name for path in lean_files
           for name in re.findall(r"\b(?:theorem|def|structure)\s+(\w+)", path.read_text())}
for row in coverage:
    names = [name for name in row["entry_points"].split(";") if name]
    if row["source_action"].startswith(("PROVE", "DEFINE_OR")):
        assert names, f"Unmapped proof obligation: {row['item_id']}"
    for name in names:
        assert name in symbols, f"Unknown certificate {name}: {row['item_id']}"
claim_rows = list(csv.DictReader((ROOT / "docs/claim-coverage.csv").open()))
assert len(claim_rows) == 37
for row in claim_rows:
    for name in filter(None, row["entry_points"].split(";")):
        assert name in symbols, f"Unknown claim certificate {name}"
print(f"Coverage checked: {len(coverage)} displays and {len(claim_rows)} prose claims.")
