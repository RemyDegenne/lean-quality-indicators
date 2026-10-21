# Audit report methods

## Coverage and flags

A target is a distinct selected theorem or complete source file. A judgment is flagged
if it reports at least one finding. Passes and judgments show completed / planned counts;
unfinished passes contribute their completed judgments. Distinct flagged targets are
counted once across passes.

Flag rates and Wilson 95% intervals use the first pass, avoiding double-counting repeated
judgments as independent targets. File audits count not-applicable judgments as unflagged;
partial and not-applicable counts appear with each table. Sol and Opus have no file-audit runs.

Library-comparison cells show **flagged / completed**, followed by **rate [95% interval]**,
separately for each model. A dash means no completed judgments; models are not pooled.

## Correlations

Matrix cells show **r [95% interval]; n=matched targets**. The coefficient is Pearson
correlation on binary flag decisions, also called phi. Cross-model cells match targets
from the first pass. Diagonal cells compare the first two independent passes and remain
blank without a repeat pass.

Intervals use paired-target percentile bootstrap resampling within each library, with
fixed seeds and the number of draws given in the report. An estimate is undefined for
constant decisions or insufficient matches. Intervals are omitted at boundary estimates,
below four matches, or when more than 2.5% of resamples are undefined. They measure sampling
uncertainty, not correctness. Sample sizes can differ between cells.

## API-equivalent expenditure

Each **$X / $Y** cell is in USD:

- **X:** recorded expenditure, including retained retry/interrupted-call usage.
- **Y:** `X / completed judgments × full-pass reference targets`. The reference is the
  largest completed pass in that table's library group.

Y uses each model's own observed cost, averaged across its passes. It is an extrapolation
when coverage is smaller; estimates from a handful of targets can be dominated by one
expensive judgment. Models with cheaper tokens can still cost more if they use more tokens.

Costs use standard short-context API rates, including recorded cache usage and reasoning
output, without adding reasoning tokens twice. GLM uses frozen OpenRouter model-list
rates, which can differ from routing prices and pi's bundled prices. Opus baselines use
their saved API-equivalent amounts because token counts were not retained.

The scope is the current audits and the original Opus duplication baseline.
Deleted or overwritten usage and this coordinating conversation are excluded; the totals
cannot reconstruct the entire historical bill. See the [cost summary and rate sources](runs/main/api-equivalent-costs.md)
and [frozen rates](pricing/api-rates-2026-10-21.json).

## Combined summary

The global table takes the union of first-pass findings: a source target is flagged if
any completed audit flags it, and counts once even when several audits flag it. Targets
match by library, source repository, pinned commit, path and (for theorems) declaration
location and name. Theorem and whole-file samples have separate denominators.
Cells show flagged / reviewed targets and Wilson 95% intervals. An asterisk marks
incomplete selected audit coverage; unflagged targets may acquire a flag as results arrive.
Models cover different sets of audits, shown in the model table, so their union rates
are not directly comparable when audit coverage differs. The retained Opus duplication
baseline also uses its earlier prompt, as noted in its individual report.

Combined correlations OR decisions over the audits with results for both models,
retaining only targets reviewed on every shared audit by both models. Each matrix cell
can therefore use a different audit set; the sets are recorded in AUDIT_RESULTS.json.
Self-correlations use only audits with a second pass. Bootstrap strata and interval
rules are the same as for individual audits. First-pass union counts exclude repeats;
judgment, pass and expenditure totals include them. A combined full-pass cost sums the
per-audit full-pass estimates for the model's selected audits, and is omitted until
every component has an estimate. It does not estimate missing model/audit combinations.
