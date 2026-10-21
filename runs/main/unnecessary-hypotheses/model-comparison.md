# Unnecessary hypotheses: comparison of judges

Same first 300 sampled theorems per library. Flags are judge claims.

| Library | claude-opus-5-5-high | rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 11/300: 3.7% (2.1%–6.4%) | 9/300: 3.0% (1.6%–5.6%) | 12/300: 4.0% (2.3%–6.9%) | 12/300: 4.0% (2.3%–6.9%) | 12/300: 4.0% (2.3%–6.9%) | 11/300: 3.7% (2.1%–6.4%) | 6/300: 2.0% (0.9%–4.3%) | 7/300: 2.3% (1.1%–4.7%) |
| Tau Ceti | 15/300: 5.0% (3.1%–8.1%) | 14/300: 4.7% (2.8%–7.7%) | 19/300: 6.3% (4.1%–9.7%) | 18/300: 6.0% (3.8%–9.3%) | 19/300: 6.3% (4.1%–9.7%) | 18/300: 6.0% (3.8%–9.3%) | 12/300: 4.0% (2.3%–6.9%) | 10/300: 3.3% (1.8%–6.0%) |
| Lean Pool | 52/300: 17.3% (13.5%–22.0%) | 48/300: 16.0% (12.3%–20.6%) | 60/300: 20.0% (15.9%–24.9%) | 61/300: 20.3% (16.2%–25.2%) | 48/300: 16.0% (12.3%–20.6%) | 51/300: 17.0% (13.2%–21.7%) | 39/300: 13.0% (9.7%–17.3%) | 42/300: 14.0% (10.5%–18.4%) |
| FLT (Anthropic) | 64/300: 21.3% (17.1%–26.3%) | 64/300: 21.3% (17.1%–26.3%) | 78/300: 26.0% (21.4%–31.2%) | 79/300: 26.3% (21.7%–31.6%) | 61/300: 20.3% (16.2%–25.2%) | 60/300: 20.0% (15.9%–24.9%) | 52/300: 17.3% (13.5%–22.0%) | 54/300: 18.0% (14.1%–22.7%) |
| Formal Frontier | 15/300: 5.0% (3.1%–8.1%) | 15/300: 5.0% (3.1%–8.1%) | 18/300: 6.0% (3.8%–9.3%) | 17/300: 5.7% (3.6%–8.9%) | 15/300: 5.0% (3.1%–8.1%) | 15/300: 5.0% (3.1%–8.1%) | 12/300: 4.0% (2.3%–6.9%) | 11/300: 3.7% (2.1%–6.4%) |

## Pairwise agreement

| First | Second | Library | Both | Either | Disagreements | Same hypothesis among both | κ |
|---|---|---|---:|---:|---:|---:|---:|
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | Mathlib | 9 | 11 | 2 | 9/9 | 0.897 |
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | Tau Ceti | 14 | 15 | 1 | 14/14 | 0.964 |
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | Lean Pool | 47 | 53 | 6 | 46/47 | 0.928 |
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | FLT (Anthropic) | 59 | 69 | 10 | 58/59 | 0.901 |
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | Formal Frontier | 14 | 16 | 2 | 14/14 | 0.930 |
| claude-opus-5-5-high | rejudge-claude-opus-5-5-high | All | 143 | 164 | 21 | 141/143 | 0.924 |
| claude-opus-5-5-high | gpt-6.1-sol-high | Mathlib | 11 | 12 | 1 | 11/11 | 0.955 |
| claude-opus-5-5-high | gpt-6.1-sol-high | Tau Ceti | 15 | 19 | 4 | 15/15 | 0.875 |
| claude-opus-5-5-high | gpt-6.1-sol-high | Lean Pool | 52 | 60 | 8 | 51/52 | 0.912 |
| claude-opus-5-5-high | gpt-6.1-sol-high | FLT (Anthropic) | 64 | 78 | 14 | 63/64 | 0.871 |
| claude-opus-5-5-high | gpt-6.1-sol-high | Formal Frontier | 15 | 18 | 3 | 15/15 | 0.904 |
| claude-opus-5-5-high | gpt-6.1-sol-high | All | 157 | 187 | 30 | 155/157 | 0.902 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Mathlib | 11 | 12 | 1 | 11/11 | 0.955 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Tau Ceti | 15 | 18 | 3 | 15/15 | 0.904 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Lean Pool | 52 | 61 | 9 | 51/52 | 0.902 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | FLT (Anthropic) | 64 | 79 | 15 | 63/64 | 0.863 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Formal Frontier | 15 | 17 | 2 | 15/15 | 0.934 |
| claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | All | 157 | 187 | 30 | 155/157 | 0.902 |
| claude-opus-5-5-high | gpt-6-luna-high | Mathlib | 8 | 15 | 7 | 7/8 | 0.684 |
| claude-opus-5-5-high | gpt-6-luna-high | Tau Ceti | 9 | 25 | 16 | 9/9 | 0.502 |
| claude-opus-5-5-high | gpt-6-luna-high | Lean Pool | 44 | 56 | 12 | 43/44 | 0.856 |
| claude-opus-5-5-high | gpt-6-luna-high | FLT (Anthropic) | 47 | 78 | 31 | 41/47 | 0.687 |
| claude-opus-5-5-high | gpt-6-luna-high | Formal Frontier | 10 | 20 | 10 | 9/10 | 0.649 |
| claude-opus-5-5-high | gpt-6-luna-high | All | 118 | 194 | 76 | 109/118 | 0.728 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Mathlib | 9 | 13 | 4 | 9/9 | 0.811 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Tau Ceti | 11 | 22 | 11 | 10/11 | 0.647 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Lean Pool | 44 | 59 | 15 | 42/44 | 0.824 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | FLT (Anthropic) | 48 | 76 | 28 | 44/48 | 0.715 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Formal Frontier | 11 | 19 | 8 | 10/11 | 0.719 |
| claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | All | 123 | 189 | 66 | 115/123 | 0.764 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | Mathlib | 6 | 11 | 5 | 6/6 | 0.698 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | Tau Ceti | 12 | 15 | 3 | 12/12 | 0.884 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | Lean Pool | 39 | 52 | 13 | 39/39 | 0.832 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | FLT (Anthropic) | 50 | 66 | 16 | 48/50 | 0.829 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | Formal Frontier | 12 | 15 | 3 | 12/12 | 0.884 |
| claude-opus-5-5-high | claude-sonnet-5-5-high | All | 119 | 159 | 40 | 117/119 | 0.842 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Mathlib | 7 | 11 | 4 | 7/7 | 0.771 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 10 | 15 | 5 | 10/10 | 0.792 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 42 | 52 | 10 | 40/42 | 0.874 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 54 | 64 | 10 | 51/54 | 0.895 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 11 | 15 | 4 | 11/11 | 0.839 |
| claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | All | 124 | 157 | 33 | 119/124 | 0.871 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | Mathlib | 9 | 12 | 3 | 9/9 | 0.852 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | Tau Ceti | 14 | 19 | 5 | 14/14 | 0.840 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | Lean Pool | 48 | 60 | 12 | 47/48 | 0.865 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | FLT (Anthropic) | 63 | 79 | 16 | 63/63 | 0.853 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | Formal Frontier | 15 | 18 | 3 | 15/15 | 0.904 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high | All | 149 | 188 | 39 | 148/149 | 0.870 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Mathlib | 9 | 12 | 3 | 9/9 | 0.852 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Tau Ceti | 14 | 18 | 4 | 14/14 | 0.868 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Lean Pool | 48 | 61 | 13 | 47/48 | 0.855 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | FLT (Anthropic) | 63 | 80 | 17 | 63/63 | 0.844 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | Formal Frontier | 15 | 17 | 2 | 15/15 | 0.934 |
| rejudge-claude-opus-5-5-high | gpt-6.1-sol-high-repeat-2 | All | 149 | 188 | 39 | 148/149 | 0.870 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | Mathlib | 7 | 14 | 7 | 7/7 | 0.655 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | Tau Ceti | 9 | 24 | 15 | 9/9 | 0.520 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | Lean Pool | 42 | 54 | 12 | 40/42 | 0.851 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | FLT (Anthropic) | 46 | 79 | 33 | 40/46 | 0.667 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | Formal Frontier | 10 | 20 | 10 | 10/10 | 0.649 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high | All | 114 | 191 | 77 | 106/114 | 0.719 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Mathlib | 8 | 12 | 4 | 8/8 | 0.793 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Tau Ceti | 10 | 22 | 12 | 10/10 | 0.604 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Lean Pool | 43 | 56 | 13 | 40/43 | 0.843 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | FLT (Anthropic) | 50 | 74 | 24 | 45/50 | 0.756 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | Formal Frontier | 11 | 19 | 8 | 11/11 | 0.719 |
| rejudge-claude-opus-5-5-high | gpt-6-luna-high-repeat-2 | All | 122 | 183 | 61 | 114/122 | 0.777 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | Mathlib | 6 | 9 | 3 | 6/6 | 0.795 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | Tau Ceti | 12 | 14 | 2 | 12/12 | 0.920 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | Lean Pool | 38 | 49 | 11 | 37/38 | 0.852 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | FLT (Anthropic) | 50 | 66 | 16 | 49/50 | 0.829 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | Formal Frontier | 12 | 15 | 3 | 11/12 | 0.884 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high | All | 118 | 153 | 35 | 115/118 | 0.858 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Mathlib | 7 | 9 | 2 | 7/7 | 0.872 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 10 | 14 | 4 | 10/10 | 0.827 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 39 | 51 | 12 | 36/39 | 0.843 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 52 | 66 | 14 | 48/52 | 0.853 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 11 | 15 | 4 | 10/11 | 0.839 |
| rejudge-claude-opus-5-5-high | claude-sonnet-5-5-high-repeat-2 | All | 119 | 155 | 36 | 111/119 | 0.856 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | Mathlib | 12 | 12 | 0 | 12/12 | 1.000 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | Tau Ceti | 18 | 19 | 1 | 18/18 | 0.971 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | Lean Pool | 60 | 61 | 1 | 58/60 | 0.990 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | FLT (Anthropic) | 78 | 79 | 1 | 78/78 | 0.991 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | Formal Frontier | 17 | 18 | 1 | 17/17 | 0.970 |
| gpt-6.1-sol-high | gpt-6.1-sol-high-repeat-2 | All | 185 | 189 | 4 | 183/185 | 0.988 |
| gpt-6.1-sol-high | gpt-6-luna-high | Mathlib | 8 | 16 | 8 | 7/8 | 0.653 |
| gpt-6.1-sol-high | gpt-6-luna-high | Tau Ceti | 9 | 29 | 20 | 9/9 | 0.438 |
| gpt-6.1-sol-high | gpt-6-luna-high | Lean Pool | 46 | 62 | 16 | 44/46 | 0.820 |
| gpt-6.1-sol-high | gpt-6-luna-high | FLT (Anthropic) | 52 | 87 | 35 | 47/52 | 0.674 |
| gpt-6.1-sol-high | gpt-6-luna-high | Formal Frontier | 10 | 23 | 13 | 10/10 | 0.583 |
| gpt-6.1-sol-high | gpt-6-luna-high | All | 125 | 217 | 92 | 117/125 | 0.697 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | Mathlib | 9 | 14 | 5 | 9/9 | 0.774 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | Tau Ceti | 13 | 24 | 11 | 12/13 | 0.683 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | Lean Pool | 47 | 64 | 17 | 45/47 | 0.812 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | FLT (Anthropic) | 54 | 84 | 30 | 50/54 | 0.719 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | Formal Frontier | 11 | 22 | 11 | 11/11 | 0.647 |
| gpt-6.1-sol-high | gpt-6-luna-high-repeat-2 | All | 134 | 208 | 74 | 127/134 | 0.756 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | Mathlib | 6 | 12 | 6 | 6/6 | 0.658 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | Tau Ceti | 12 | 19 | 7 | 12/12 | 0.763 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | Lean Pool | 39 | 60 | 21 | 39/39 | 0.748 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | FLT (Anthropic) | 51 | 79 | 28 | 51/51 | 0.728 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | Formal Frontier | 12 | 18 | 6 | 12/12 | 0.790 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high | All | 120 | 188 | 68 | 120/120 | 0.755 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | Mathlib | 7 | 12 | 5 | 7/7 | 0.729 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 10 | 19 | 9 | 10/10 | 0.675 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 42 | 60 | 18 | 40/42 | 0.789 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 54 | 78 | 24 | 53/54 | 0.769 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 11 | 18 | 7 | 11/11 | 0.747 |
| gpt-6.1-sol-high | claude-sonnet-5-5-high-repeat-2 | All | 124 | 187 | 63 | 121/124 | 0.775 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | Mathlib | 8 | 16 | 8 | 7/8 | 0.653 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | Tau Ceti | 9 | 28 | 19 | 9/9 | 0.453 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | Lean Pool | 46 | 63 | 17 | 44/46 | 0.810 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | FLT (Anthropic) | 52 | 88 | 36 | 47/52 | 0.666 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | Formal Frontier | 10 | 22 | 12 | 10/10 | 0.604 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high | All | 125 | 217 | 92 | 117/125 | 0.697 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | Mathlib | 9 | 14 | 5 | 9/9 | 0.774 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | Tau Ceti | 13 | 23 | 10 | 12/13 | 0.704 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | Lean Pool | 47 | 65 | 18 | 45/47 | 0.803 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | FLT (Anthropic) | 54 | 85 | 31 | 50/54 | 0.711 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | Formal Frontier | 11 | 21 | 10 | 11/11 | 0.670 |
| gpt-6.1-sol-high-repeat-2 | gpt-6-luna-high-repeat-2 | All | 134 | 208 | 74 | 127/134 | 0.756 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | Mathlib | 6 | 12 | 6 | 6/6 | 0.658 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | Tau Ceti | 12 | 18 | 6 | 12/12 | 0.790 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | Lean Pool | 39 | 61 | 22 | 39/39 | 0.739 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | FLT (Anthropic) | 51 | 80 | 29 | 51/51 | 0.720 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | Formal Frontier | 12 | 17 | 5 | 11/12 | 0.819 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high | All | 120 | 188 | 68 | 119/120 | 0.755 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Mathlib | 7 | 12 | 5 | 7/7 | 0.729 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 10 | 18 | 8 | 10/10 | 0.701 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 42 | 61 | 19 | 40/42 | 0.779 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 54 | 79 | 25 | 53/54 | 0.761 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 11 | 17 | 6 | 10/11 | 0.776 |
| gpt-6.1-sol-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | All | 124 | 187 | 63 | 120/124 | 0.775 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | Mathlib | 7 | 16 | 9 | 7/7 | 0.593 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | Tau Ceti | 12 | 25 | 13 | 12/12 | 0.626 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | Lean Pool | 43 | 56 | 13 | 38/43 | 0.843 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | FLT (Anthropic) | 44 | 77 | 33 | 41/44 | 0.658 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | Formal Frontier | 11 | 19 | 8 | 11/11 | 0.719 |
| gpt-6-luna-high | gpt-6-luna-high-repeat-2 | All | 117 | 193 | 76 | 109/117 | 0.727 |
| gpt-6-luna-high | claude-sonnet-5-5-high | Mathlib | 4 | 14 | 10 | 4/4 | 0.429 |
| gpt-6-luna-high | claude-sonnet-5-5-high | Tau Ceti | 9 | 22 | 13 | 9/9 | 0.559 |
| gpt-6-luna-high | claude-sonnet-5-5-high | Lean Pool | 36 | 51 | 15 | 34/36 | 0.799 |
| gpt-6-luna-high | claude-sonnet-5-5-high | FLT (Anthropic) | 41 | 72 | 31 | 36/41 | 0.663 |
| gpt-6-luna-high | claude-sonnet-5-5-high | Formal Frontier | 10 | 17 | 7 | 9/10 | 0.729 |
| gpt-6-luna-high | claude-sonnet-5-5-high | All | 100 | 176 | 76 | 92/100 | 0.697 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | Mathlib | 6 | 13 | 7 | 6/6 | 0.620 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 8 | 21 | 13 | 8/8 | 0.531 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 38 | 52 | 14 | 34/38 | 0.817 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 42 | 73 | 31 | 34/42 | 0.667 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 9 | 17 | 8 | 8/9 | 0.679 |
| gpt-6-luna-high | claude-sonnet-5-5-high-repeat-2 | All | 103 | 176 | 73 | 90/103 | 0.712 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | Mathlib | 5 | 12 | 7 | 4/5 | 0.577 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | Tau Ceti | 9 | 21 | 12 | 9/9 | 0.580 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | Lean Pool | 37 | 53 | 16 | 36/37 | 0.792 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | FLT (Anthropic) | 44 | 68 | 24 | 39/44 | 0.737 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | Formal Frontier | 11 | 16 | 5 | 10/11 | 0.806 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high | All | 106 | 170 | 64 | 98/106 | 0.745 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Mathlib | 7 | 11 | 4 | 7/7 | 0.771 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 8 | 20 | 12 | 8/8 | 0.552 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 38 | 55 | 17 | 35/38 | 0.784 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 45 | 69 | 24 | 40/45 | 0.740 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 10 | 16 | 6 | 9/10 | 0.759 |
| gpt-6-luna-high-repeat-2 | claude-sonnet-5-5-high-repeat-2 | All | 108 | 171 | 63 | 99/108 | 0.751 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | Mathlib | 5 | 8 | 3 | 5/5 | 0.764 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | Tau Ceti | 10 | 12 | 2 | 10/10 | 0.906 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | Lean Pool | 35 | 46 | 11 | 33/35 | 0.843 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | FLT (Anthropic) | 47 | 59 | 12 | 44/47 | 0.863 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | Formal Frontier | 11 | 12 | 1 | 11/11 | 0.955 |
| claude-sonnet-5-5-high | claude-sonnet-5-5-high-repeat-2 | All | 108 | 137 | 29 | 103/108 | 0.871 |
