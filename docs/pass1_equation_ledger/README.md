# Pass 1 equation ledger

The source display inventory is sharded only to keep each audit file small and reviewable. Together the five CSV files contain every displayed mathematical block in the supplied LaTeX source package.

| File | Items | Range |
|---|---:|---|
| `part_01.csv` | 50 | M001–M050 |
| `part_02.csv` | 50 | M051–M100 |
| `part_03.csv` | 50 | M101–M150 |
| `part_04.csv` | 50 | M151–S041 |
| `part_05.csv` | 6 | S042–S047 |

Total: **206 display blocks** = 159 from `main.tex` + 47 from `supplementary_material.tex`.

Each row records the exact source file and line span, manuscript label when present, formalisation action, target theorem bundle, a short SHA-256 fingerprint of the extracted formula, and a formula preview. The frozen source-file hashes are recorded in `../PASS1_SOURCE_SPEC.md`.
