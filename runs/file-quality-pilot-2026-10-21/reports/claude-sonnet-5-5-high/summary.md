# File quality pilot

Judge: `claude-sonnet-5-5-high`. Unit: one complete source file.

Cells: files with findings / completed reviews (number of findings). The same files are used for every rubric.

| Rubric | Mathlib | Tau Ceti | Lean Pool |
|---|---:|---:|---:|
| concept-reinvention | 3/10 (5); 1 N/A | 0/10 (0); 4 N/A | 5/10 (9); 1 N/A |
| statement-generality | 6/10 (6) | 3/10 (3) | 9/10 (13) |
| vacuity-and-misstatement | 3/10 (3) | 0/10 (0) | 2/10 (3) |
| missing-structure | 3/10 (4); 1 N/A | 2/10 (2); 4 N/A | 3/10 (5) |
| simp-interface | 4/10 (7); 1 N/A | 3/10 (3) | 6/10 (9) |
| fragile-proofs | 9/10 (19) | 8/10 (14) | 9/10 (26) |
| repeated-proof-machinery | 4/10 (8) | 4/10 (5) | 8/10 (18) |
| readable-proof-simplification | 7/10 (10) | 8/10 (14) | 9/10 (23) |

Completed judgments: 240/240.

Flags are judge claims; replacements have not been compiled or independently audited. This small file sample does not estimate a theorem defect rate. Rubrics may flag the same issue.
