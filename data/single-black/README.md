# Single black cell certificate data

These files were produced by exploration scripts. They are **not** part of the trust chain: every
parameter is re-checked by the Lean kernel, and a wrong value can only make a check fail.

| File | Content |
| --- | --- |
| `single_black_params.json` | Search results from `scripts/find_single_black.py`: for each early cell, the black cell `q`, step count `T`, entry heading, translation `w` and entry origin `o` |
| `cell-style.json` | Certificate form used by each cell: `old` = `checkSingleBlack`, `fast` / `fast2` = `checkSingleBlackFast` / `checkSingleBlackFast2`, `seg` = segmented (`SegmentCheck`) |
| `segment-plan.json` | For each segmented cell, the number of 12000-step segments |
| `seg-cells.txt` | The 34 cells that use the segmented certificate |
| `data49.json` | The 937 junk cells for the phase-49 blank case (literal list in `Phase49Data.lean`) |
