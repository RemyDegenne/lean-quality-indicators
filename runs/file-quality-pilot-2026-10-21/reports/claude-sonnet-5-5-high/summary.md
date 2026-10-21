# File quality pilot

Judge: `claude-sonnet-5-5-high`. Unit: one complete source file.

Cells: files with findings / completed reviews (number of findings). The same files are used for every rubric.

| Rubric | Mathlib | Tau Ceti | Lean Pool |
|---|---:|---:|---:|
| concept-reinvention | 1/4 (2); 1 N/A | 0/4 (0); 1 N/A | 2/4 (4); 1 N/A |
| statement-generality | 2/4 (2) | 1/4 (1) | 3/4 (4) |
| vacuity-and-misstatement | 2/4 (2) | 0/3 (0) | 1/3 (1) |
| missing-structure | 1/3 (2) | 1/3 (1); 1 N/A | 2/3 (3) |
| simp-interface | 1/3 (1); 1 N/A | 0/3 (0) | 2/3 (4) |
| fragile-proofs | 2/3 (4) | 2/3 (3) | 2/3 (8) |
| repeated-proof-machinery | 2/3 (3) | 1/3 (2) | 2/3 (4) |
| readable-proof-simplification | 2/3 (2) | 2/3 (3) | 2/3 (5) |

Completed judgments: 79/240.

Flags are judge claims; replacements have not been compiled or independently audited. This small file sample does not estimate a theorem defect rate. Rubrics may flag the same issue.
