# Explicit unfoldings of definitions, by library

Source backend of [def_unfolds.py](../../scripts/def_unfolds.py) on every `def`/`abbrev` of each library, in the scope of the other audits. A definition is *used* in a scope when its name occurs there, and *unfolded* there when it occurs in `unfold`/`delta`/`unseal`, as a bare item of a `simp`-like or `rw`-like list, or through an equation lemma (`foo.eq_def`). The directory of a definition includes its subdirectories. Every definition is counted (no sampling).

Against Lean's own name resolution ([README](README.md)), the source backend finds about 99% of the unfoldings, with about 99% precision, but misses part of the uses (field notation on expressions, overloaded names): the counts of definitions used and of uses are lower bounds, so the shares and rates per use are slightly high.

## Outside the definition's file

| Library | Files | Definitions | Used there | Unfolded there | Share | Uses | Unfoldings | unfold | simp | rw | eq_def | Per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 8,175 | 34,098 | 15,006 | 2,858 | 19.0% | 365,655 | 10,692 | 370 | 7,160 | 3,146 | 16 | 2.92 |
| Tau Ceti | 16,726 | 23,273 | 14,775 | 308 | 2.1% | 337,956 | 1,054 | 32 | 772 | 234 | 16 | 0.31 |
| Lean Pool | 21,182 | 74,932 | 38,513 | 16,390 | 42.6% | 1,832,109 | 97,384 | 22,478 | 67,389 | 7,483 | 34 | 5.32 |
| FLT (Anthropic) | 30,962 | 78,206 | 6,683 | 2,425 | 36.3% | 2,429,825 | 48,528 | 13,195 | 21,484 | 13,849 | 0 | 2.00 |
| Formal Frontier | 1,342 | 3,821 | 1,416 | 133 | 9.4% | 19,369 | 299 | 22 | 244 | 33 | 0 | 1.54 |
| OpenAI Math | 121,797 | 1,117,060 | 322,130 | 145,562 | 45.2% | 9,393,492 | 597,987 | 236,695 | 342,343 | 18,801 | 148 | 6.37 |
| CFSG (AxiomMath) | 194,203 | 275,245 | 168,869 | 40,449 | 24.0% | 9,647,389 | 233,224 | 44,256 | 134,209 | 54,701 | 58 | 2.42 |

## Outside the definition's directory

| Library | Files | Definitions | Used there | Unfolded there | Share | Uses | Unfoldings | unfold | simp | rw | eq_def | Per 100 uses |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 8,175 | 34,098 | 10,234 | 1,686 | 16.5% | 244,719 | 6,207 | 189 | 4,162 | 1,849 | 7 | 2.54 |
| Tau Ceti | 16,726 | 23,273 | 8,504 | 118 | 1.4% | 147,446 | 393 | 11 | 243 | 123 | 16 | 0.27 |
| Lean Pool | 21,182 | 74,932 | 8,790 | 3,071 | 34.9% | 542,832 | 24,309 | 4,063 | 18,574 | 1,661 | 11 | 4.48 |
| FLT (Anthropic) | 30,962 | 78,206 | 6,460 | 2,390 | 37.0% | 2,392,836 | 47,712 | 13,075 | 21,052 | 13,585 | 0 | 1.99 |
| Formal Frontier | 1,342 | 3,821 | 199 | 12 | 6.0% | 2,360 | 27 | 1 | 23 | 3 | 0 | 1.14 |
| OpenAI Math | 121,797 | 1,117,060 | 109,261 | 32,351 | 29.6% | 4,394,029 | 264,123 | 126,932 | 132,734 | 4,409 | 48 | 6.01 |
| CFSG (AxiomMath) | 194,203 | 275,245 | 49,991 | 10,348 | 20.7% | 5,149,791 | 102,338 | 19,231 | 60,935 | 22,159 | 13 | 1.99 |

## Exact counts for the built libraries

Lean's own name resolution (ilean backend, on the `.ilean` files of a build restored from the library's cache at the same commit), next to the source backend. The unfoldings agree; the source backend misses part of the uses, so its shares and rates per use are higher. Comparisons in [ilean/mathlib/comparison.md](ilean/mathlib/comparison.md), [ilean/tauceti/comparison.md](ilean/tauceti/comparison.md).

| Library | Backend | Used outside file | Unfolded there | Share | Per 100 uses | Used outside directory | Unfolded there | Share | Per 100 uses |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | Lean | 16,432 | 2,857 | 17.4% | 2.31 | 11,292 | 1,688 | 14.9% | 1.95 |
| Mathlib | source | 15,006 | 2,858 | 19.0% | 2.92 | 10,234 | 1,686 | 16.5% | 2.54 |
| Tau Ceti | Lean | 15,312 | 308 | 2.0% | 0.28 | 9,070 | 119 | 1.3% | 0.23 |
| Tau Ceti | source | 14,775 | 308 | 2.1% | 0.31 | 8,504 | 118 | 1.4% | 0.27 |

Sources: Mathlib `e3e75e86143b`; Tau Ceti `e8b7b600c36c`; Lean Pool `01db1d7049cf`; FLT (Anthropic) `6e837e753555`; Formal Frontier (43 repositories); OpenAI Math `1581d4cbdd69`; CFSG (AxiomMath) `5f8042b343bd`.
