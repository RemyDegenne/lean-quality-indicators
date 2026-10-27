# Repeated proof machinery: validation

Sonnet 5.5 high, lean-fro subscription. Twenty flagged and ten unflagged files per library, excluding the earlier manual sample. Candidate checks try to refute the original findings; discovery tasks search for missed findings. Results are source-based, not compiled verification. This is not a new first pass and does not change the main flag rates.

| Library | Original flags / reviewed | Flagged checked | Supported | Unsupported | Uncertain | Unflagged checked | Misses found | API-equivalent USD |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| mathlib | 60/372 | 11/20 | 5 | 5 | 1 | 5/10 | 0 | $1.69 |
| tauceti | 64/372 | 11/20 | 2 | 9 | 0 | 5/10 | 0 | $1.41 |
| formal-frontier | 128/372 | 11/20 | 8 | 3 | 0 | 5/10 | 0 | $1.22 |
| lean-pool | 180/372 | 11/20 | 8 | 3 | 0 | 5/10 | 0 | $1.81 |
| flt-anthropic | 189/372 | 9/20 | 5 | 4 | 0 | 5/10 | 0 | $2.39 |
| openai-math | 154/372 | 10/20 | 6 | 4 | 0 | 5/10 | 0 | $1.66 |

Supported means at least one supplied claim is confirmed or a new qualifying finding is found. Unsupported requires all supplied claims refuted and complete coverage; uncertainty is separate. The JSON report includes Wilson intervals for conditional support and missed-finding fractions. These measure small-sample uncertainty, not correctness or inter-model agreement.

Coverage expansion to 500 files per library remains conditional on reviewing these validation results.
