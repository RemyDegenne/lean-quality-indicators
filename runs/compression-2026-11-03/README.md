# Compression ratio of the sources (2026-11-03)

[compression.py](../../scripts/compression.py) compresses the source of each library, in
the scope of the other audits, with zstd at level 19. It reports original size / compressed
size: the higher, the more repetitive the text. No sampling and no LLM. Commands are in
[RUNNING.md](../../RUNNING.md#compression-ratio).

## Results

Code only (comments, string literals and blank lines removed). [results.md](results.md) has
the source as is, the other chunk sizes, the spread across chunks and the most
compressible files.

| Library | MB of code | Per file | 1 MB chunks | 8 MB chunks | Whole library | Lines in another file |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 75.8 | 4.08 | 5.77 | 6.19 | 6.39 | 3.8% |
| Tau Ceti | 110.5 | 4.05 | 6.80 | 7.38 | 7.60 | 10.5% |
| Lean Pool | 314.3 | 5.77 | 8.35 | 9.02 | 9.41 | 20.1% |
| FLT (Anthropic) | 851.4 | 5.20 | 9.64 | 12.36 | 15.56 | 60.5% |
| Formal Frontier | 10.8 | 4.64 | 7.20 | 7.62 | 7.72 | 8.0% |
| OpenAI Math | 1,464.6 | 5.37 | 8.31 | 9.23 | 9.89 | 25.4% |
| CFSG (AxiomMath) | 1,922.9 | 3.83 | 6.16 | 6.89 | 7.56 | 27.5% |

The five scales:
- **Per file:** each file compressed alone, which measures repetition inside a file.
- **Chunks:** the files concatenated in path order and cut into chunks of 64 KB, 1 MB and
  8 MB, each compressed alone. This measures repetition between neighbouring files. Every
  chunk has the same size, so these ratios can be compared across libraries.
- **Whole library:** everything compressed at once. This ratio also grows with the size of
  the library, so it is not comparable across libraries.

**Lines in another file** is the share of code lines found verbatim in another file of the
library. Only lines of at least 40 characters once stripped count, and `import`,
`set_option` and `open` lines are left out.

Reading notes:

- Mathlib compresses least in 1 MB and 8 MB chunks and as a whole, and repeats the fewest
  lines across files (3.8%). At the smallest scales CFSG compresses slightly less than
  Mathlib: 3.83 against 4.08 per file, and 4.76 against 4.81 in 64 KB chunks.
- FLT repeats the most. 60.5% of its code lines occur verbatim in another file, and its
  ratio keeps rising with the window: 5.2 per file, 9.6 for 1 MB chunks, 15.6 for the
  whole library. The most repeated lines are binders, instance attributes and proof steps
  (`refine Finset.sum_congr rfl fun i _ => ?_` in 1,354 files).
- OpenAI Math and Lean Pool have long tails: 10% of their 1 MB chunks compress more than
  28× and 19× respectively. Their most compressible files are generated tables and
  templates, which the `*/Certificates/*` exclusion of the other audits does not catch:
  - Lean Pool's `BrillNoetherGraphs/LowGenus/Generated/`;
  - OpenAI Math's `SnakyConditional/Templates/`.
- CFSG is where the two measures disagree. In chunks it compresses about as little as
  Mathlib (6.2 against 5.8 for 1 MB), yet 27.5% of its lines also occur in another file.
  - Most of these copies are small: of 1.43M distinct repeated lines, 1.34M occur in only
    2 to 5 files.
  - More than half (55%) have copies more than 200 files apart in path order. A 1 MB chunk
    holds about 100 CFSG files, so the chunks do not see these copies.
  - The whole-library ratio does see them, but it is only 7.6. The rest of CFSG's text is
    probably hard to predict: for example hash-like names (`Yardstones.Md0ec50421ce4`) and
    numeric data.
  - The most repeated lines are boilerplate:
    `have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩` occurs in 20,886 files.
- Compression does not tell systematic API from copy-paste. Mathlib's most compressible
  file (`CategoryTheory/Limits/Preserves/Opposites.lean`, 14×) states each lemma for `op`,
  `leftOp`, `rightOp` and `unop`.
- Comments and blank lines make up 20.4% of Mathlib's bytes and 37.6% of Tau Ceti's,
  against 1.4% to 4.9% for FLT, OpenAI Math and CFSG. Prose and code compress differently,
  so the table above is on code only.

One directory per library, each with `summary.json` (every measure) and `meta.json`
(commits, zstd version). `files.jsonl` has every file's sizes and line counts; it is not
versioned and `scripts/compression.py` regenerates it. A second run gave identical
compressed sizes.
