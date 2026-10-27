# Repeated proof machinery: validation

Sonnet 5.5 high, lean-fro subscription. Twenty flagged and ten unflagged files per library, excluding the earlier manual sample. Candidate checks try to refute the original findings; discovery tasks search for missed findings. Results are source-based, not compiled verification. This is not a new first pass and does not change the main flag rates.

| Library | Original flags / reviewed | Flagged checked | Supported | Unsupported | Uncertain | Unflagged checked | Misses found | API-equivalent USD |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| mathlib | 60/372 | 18/20 | 9 | 8 | 1 | 9/10 | 0 | $2.40 |
| tauceti | 64/372 | 18/20 | 3 | 15 | 0 | 9/10 | 0 | $2.22 |
| formal-frontier | 128/372 | 18/20 | 12 | 6 | 0 | 9/10 | 0 | $2.00 |
| lean-pool | 180/372 | 18/20 | 11 | 6 | 1 | 9/10 | 0 | $2.97 |
| flt-anthropic | 189/372 | 17/20 | 12 | 5 | 0 | 9/10 | 0 | $4.48 |
| openai-math | 154/372 | 18/20 | 10 | 8 | 0 | 9/10 | 0 | $3.42 |

Supported means at least one supplied claim is confirmed or a new qualifying finding is found. Unsupported requires all supplied claims refuted and complete coverage; uncertainty is separate. The JSON report includes Wilson intervals for conditional support and missed-finding fractions. These measure small-sample uncertainty, not correctness or inter-model agreement.

Coverage expansion to 500 files per library remains conditional on reviewing these validation results.
