# Review of the repeated-machinery findings

All 30 Sonnet file/rubric judgments completed on the frozen sample of ten files each from Mathlib, Tau Ceti and Lean Pool. Every reported positive was reviewed: 17 repeated-proof-machinery findings. Raw judgments are unchanged.

The review checked the actual source, supporting uses and APIs, hypotheses, proposed lemmas and rewritten uses. Proposed replacements have not been compiled. The review covers positives only and does not assess missed findings.

| Findings reviewed | Would pursue | Qualified / optional |
|---:|---:|---:|
| 17 | 11 | 6 |

Repeated-machinery provides eleven candidates worth pursuing: the scalar perturbation estimate; four cutoff/integral refactors; the shared Gaussian-phase bound; dyadic-shell existence and disjointness; the cyclic-plus-skew Killing-form identity; torus/cell pairing; and reuse of the existing coordinate-change continuity theorem. Six other proposals are plausible short cleanups or thin wrappers. Some cutoff findings overlap in one larger refactor.

- **pursue**: A source-supported improvement candidate I would pursue; exact replacement remains uncompiled.
- **qualified**: An optional or incomplete refactoring idea whose compliance with the rubric or net benefit is not established.

## repeated-proof-machinery


### lean-pool: zero_mem_convexHull_of_best_approx (inner h_active, both by_cases branches)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L190-L248) — **pursue**.

The scalar lemma is true with the stated sign and absolute-value hypotheses. Its proof isolates the substantial duplicated positive/negative estimate; both original branches are replaced by one common application. The rewritten product-positivity tactic sketch needs adjustment, as Sonnet acknowledges, but the two existing sign facts give that hypothesis directly by positive-positive or negative-negative multiplication. This is a worthwhile shared mathematical argument with a credible complete refactor.

Additional inspected sources:

- [LeanPool/KaltonRoberts/DualCert.lean:187](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L187)
- [LeanPool/KaltonRoberts/DualCert.lean:190](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L190)
- [LeanPool/KaltonRoberts/DualCert.lean:221](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L221)

### lean-pool: realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree (and the wrappers realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree)

[lean-pool-file-0002 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L368-L415) — **qualified**.

The supplied helpers and rewritten Leray/Stokes applications fit the actual definitions, and could shorten the concrete theorems. However, the repeated reasoning is generic Lp a.e.-equality transport and one existing weak-divergence congruence application. The core Fourier-to-divergence-free theorem is already shared. These are thin API wrappers of the sort the new rubric excludes, so I regard this as optional cleanup rather than a strong repeated-mathematics finding.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:364](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:384](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:394](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L394)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean:219](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean#L219)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean:652](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean#L652)

### lean-pool: pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta and pv_cutoff_integral_seg1_eq_inv / pv_cutoff_integral_seg2_eq_Ialpha / pv_cutoff_integral_seg3_eq_neg_inv

[lean-pool-file-0003 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L504-L513) — **pursue**.

The cutoff evaluations are substantial repeated computations with exactly matching segment hypotheses. The three shared statements and proof sketches reuse the existing integrand and norm lemmas, while the shown integrability and integral-congruence applications eliminate both copies. The cited congr_uIoo and integral_congr_Ioo_of_le APIs exist in the pinned Mathlib. This is a clear candidate; the snippets still need elaboration checking.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:358](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:380](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L380)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:412](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L412)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:504](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L504)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:526](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L526)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:557](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L557)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:110`
- `repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1253`

### lean-pool: pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta (a.e. transfer from Ioo to integrability) and pv_cutoff_integral_seg*_eq_* (a.e. transfer for integral equality)

[lean-pool-file-0003 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L364-L370) — **pursue**.

The six blocks reconstruct the same open-interval to interval-integral a.e. transfer, for which the pinned Mathlib already supplies exact congruence theorems. The replacement expressions have the correct direction and interval restrictions. Reusing those theorems removes substantial repeated measure-theory bookkeeping without a new wrapper or helper. This overlaps the segment-evaluation refactor but is a distinct concrete simplification.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:364](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L364)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:391](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L391)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:434](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L434)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:514](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L514)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:537](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L537)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:571](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L571)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:110`
- `repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1253`

### lean-pool: pv_cutoff_F_integrable_0_delta / pv_cutoff_F_integrable_3delta_3 and the hI1 / hI5 blocks of pv_sector_cutoff_eq

[lean-pool-file-0003 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593-L610) — **pursue**.

The same two endpoint cutoff-vanishing estimates are proved independently for integrability and for zero integrals. Pointwise zero lemmas on the closed endpoint intervals cover both uses and retain the actual positivity and cutoff assumptions. The proposal shows both kinds of rewritten application and isolates the shared mathematical estimates.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:317](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L317)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:334](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L334)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:593](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:602](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L602)

### lean-pool: log_cancellation (duplicates integral_seg1_eq_neg_log / integral_seg3_eq_log)

[lean-pool-file-0003 finding 3](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L291-L297) — **pursue**.

The existing reciprocal-integral lemmas have exactly the two required real integral statements at ε/r, and their hypotheses are already established locally. The proposed two applications remove the duplicated change-of-variable calculation and log evaluation with no new abstraction. The complex-cast steps remain intact.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:255](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L255)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:260](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L260)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:288](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:291](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L291)

### lean-pool: norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le

[lean-pool-file-0004 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428) — **pursue**.

The proposed lemma collects the full repeated phase-growth versus Gaussian-decay argument, with a precise norm-majorant hypothesis. Factoring the common exponential from each derivative expression gives the two indicated uses with their actual polynomial prefactors; the prefactor estimates stay specific to each theorem. This is a coherent shared bound with a credible net simplification, rather than just a new name for the final existing exponential inequality. The existing exponential estimate supplies the proof; the sketches still need elaboration.

Additional inspected sources:

- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:328](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:943](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L943)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:1108](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1108)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean:44](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean#L44)

### lean-pool: exists_positive_shell

[lean-pool-file-0005 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L127) — **pursue**.

The source repeats a substantial floor/log construction with the same radius bounds. The common integer-shell statement is valid under positivity, and the two sign arguments recover exactly the original natural-index and negative-integer-index statements. Both rewritten applications are given, including how positivity and the toNat conversion are obtained. The proposed placement in Kernel is compatible with the existing import direction.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean:93](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean:178](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean#L178)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/Data/Int/Log.lean:96`

### lean-pool: positiveShell_pairwise

[lean-pool-file-0005 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L161) — **pursue**.

Integer-shell disjointness is the same geometric argument in the two proofs, including mirrored branches and cast bookkeeping. A single ordered-index disjointness statement has the right hypotheses; both pairwise results then follow by order splitting and injective index casts. Exact coercion terms remain uncompiled, as acknowledged, but the mathematical abstraction and its two uses are concrete and remove substantial repetition.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean:138](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean:217](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean#L217)

### lean-pool: weakPathRepresentative_pairing_eq_inner and FrozenDriftProblem.initial_pairing_eq_cell_integral

[lean-pool-file-0007 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L206-L263) — **pursue**.

The two long calc blocks prove the same torus-L2-to-unit-cube pairing identity in opposite directions. The proposed shared statement has the right a.e.-representative hypothesis, and both supplied rewritten applications fit the existing coeFn_toLp and pointwise representative equalities. The underlying torus integral-transfer theorem applies to arbitrary functions, so no extra periodicity assumption on g is missing. This isolates substantial common measure and representation bookkeeping.

Additional inspected sources:

- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:188](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188)
- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:230](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L230)
- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean:195](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean#L195)

### mathlib: IsBigO.mul_atTop_rpow_of_isBigO_rpow / IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow

[mathlib-file-0003 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293) — **qualified**.

The pointwise inequality, its proof sketch and both rewritten uses fit the existing Eventually.isBigO signature, which asks for a norm bound by a real-valued function. The proposed refactor is mathematically sound. However, it extracts only a few direct rpow/norm calculation steps and adds a helper statement and name. This is an optional refactor rather than clear nontrivial repeated reasoning under the new rubric.

Additional inspected sources:

- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:274](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274)
- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:284](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L284)
- [Mathlib/Analysis/Asymptotics/Basic.lean:365](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Asymptotics/Basic.lean#L365)

### mathlib: Complex.isBigO_cpow_rpow / Complex.isTheta_cpow_rpow

[mathlib-file-0003 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L185-L206) — **qualified**.

Both tails use the already-shared isTheta_exp_arg_mul_im theorem followed by division by one. The proposed helper and two rewritten uses are plausible, but would package two routine steps in a fairly long new statement. The source does not demonstrate a clear complete-code improvement or substantial repeated mathematical reasoning. This remains optional API convenience.

Additional inspected sources:

- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:176](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L176)
- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:185](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L185)
- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:196](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L196)

### mathlib: Bundle.Trivialization.mk_coordChangeL and VectorPrebundle.mk_coordChange

[mathlib-file-0006 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L323) — **qualified**.

The two complete replacement proofs use existing mk_proj_snd' lemmas with the right base-set hypothesis, and look like sensible small cleanups. No new helper is needed. The duplicated portion, however, is a short projection calculation rather than nontrivial mathematical reasoning. I would not count this as a strong finding under the current repeated-machinery rubric, despite the useful replacement.

Additional inspected sources:

- [Mathlib/Topology/VectorBundle/Basic.lean:316](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316)
- [Mathlib/Topology/VectorBundle/Basic.lean:858](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L858)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:129](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L129)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:445](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L445)

### mathlib: Bundle.Trivialization.coordChangeL (continuous_toFun / continuous_invFun fields)

[mathlib-file-0006 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L275-L292) — **pursue**.

Both continuous-equivalence fields repeat the continuity-of-coordinate-change argument, and the general continuous_coordChange theorem is already available from the fiber-bundle API. The provided argument identifies each positive-branch function using mk_symm and applies that theorem with the two trivializations in opposite orders. This removes actual topological reasoning without adding a new abstraction. The exact elaboration needs checking; the later coordChangeL_apply' lemma must not be used to justify coordChangeL's own construction.

Additional inspected sources:

- [Mathlib/Topology/VectorBundle/Basic.lean:270](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L270)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:753](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L753)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:783](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L783)

### tauceti: continuousOn_schwarzChristoffelBoundary / schwarzChristoffelBoundary_sub_eq / schwarzChristoffelBoundary_injOn / collinear_schwarzChristoffelBoundary_image

[tauceti-file-0004 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L199-L259) — **qualified**.

The EqOn statement is valid and its rewritten consumers are much more concrete. The pinned InjOn.congr and EqOn.image_eq APIs support the indicated directions, and the helper would shorten the image-set proof. However, it is a one-line wrapper around the existing pointwise boundary identification plus ordinary congruence; the mathematical uniqueness argument is already shared. This is useful optional API cleanup, but the new rubric explicitly excludes thin wrappers rather than treating every such extraction as nontrivial repeated reasoning.

Additional inspected sources:

- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean:167](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L167)
- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean:225](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L225)
- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean:237](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L237)
- `repos/deps/mathlib-22c725c48122/Mathlib/Data/Set/Function.lean:74`
- `repos/deps/mathlib-22c725c48122/Mathlib/Data/Set/Function.lean:268`

### tauceti: TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg

[tauceti-file-0005 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L91-L102) — **pursue**.

The common cyclic-plus-skew Killing-form identity is a natural mathematical intermediate, and both rewritten consumers separate it from their additional product or involution hypotheses. Its placement in their common Symmetry dependency is appropriate. The suggested linarith finish is not justified over an arbitrary characteristic-zero field; after the cyclic/skew rewrites the result follows by equality symmetry and neg_mul instead. That is a small proof-sketch repair, not a problem with the proposed shared identity.

Additional inspected sources:

- [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean:93](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L93)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean:98](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean#L98)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean)

### tauceti: TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg

[tauceti-file-0005 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L103-L108) — **qualified**.

The repeated nonvanishing application and scalar rearrangement are real, and the proposed small lemmas could shorten several sites. However, one helper is a direct wrapper around an existing Killing-form theorem, and the other multiplies the supplied ratio by a scalar and rearranges products. Those are the thin wrappers and short calculations explicitly excluded by this rubric. This is optional API cleanup, rather than a convincing nontrivial repeated argument.

Additional inspected sources:

- [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean:103](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L103)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean:163](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean#L163)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/FourTerm.lean:214](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/FourTerm.lean#L214)
- [TauCeti/Algebra/Lie/Weights/Chevalley/Involution.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/Chevalley/Involution.lean)
