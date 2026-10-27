# Repeated proof machinery: validation

Sonnet 5.5 high, lean-fro subscription. Twenty flagged and ten unflagged files per library, excluding the earlier manual sample. Candidate checks try to refute the original findings; discovery tasks search for missed findings. Results are source-based, not compiled verification. This is not a new first pass and does not change the main flag rates.

| Library | Original flags / reviewed | Flagged checked | Supported | Unsupported | Uncertain | Unflagged checked | Misses found | API-equivalent USD |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| mathlib | 60/372 | 13/20 | 5 | 7 | 1 | 7/10 | 0 | $1.93 |
| tauceti | 64/372 | 13/20 | 3 | 10 | 0 | 7/10 | 0 | $1.76 |
| formal-frontier | 128/372 | 14/20 | 10 | 4 | 0 | 7/10 | 0 | $1.54 |
| lean-pool | 180/372 | 14/20 | 9 | 4 | 1 | 7/10 | 0 | $2.29 |
| flt-anthropic | 189/372 | 11/20 | 6 | 5 | 0 | 6/10 | 0 | $3.04 |
| openai-math | 154/372 | 13/20 | 8 | 5 | 0 | 6/10 | 0 | $2.08 |

Supported means at least one supplied claim is confirmed or a new qualifying finding is found. Unsupported requires all supplied claims refuted and complete coverage; uncertainty is separate. The JSON report includes Wilson intervals for conditional support and missed-finding fractions. These measure small-sample uncertainty, not correctness or inter-model agreement.

Coverage expansion to 500 files per library remains conditional on reviewing these validation results.
