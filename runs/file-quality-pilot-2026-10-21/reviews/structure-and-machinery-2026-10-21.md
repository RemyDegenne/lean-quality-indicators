# Review of the structured-interface and repeated-machinery findings

All 38 current Sonnet findings were reviewed: 9 missing-structure and 29 repeated-proof-machinery, across all three libraries. Raw judgments are unchanged.

This is a source review, including relevant APIs, supporting proof blocks and polynomial import dependencies. Proposed replacements have not been compiled. The assessment counts are reviewer judgments about candidates, not verified defects or an accuracy estimate.

| Rubric | Findings reviewed | Would pursue | Qualified / optional | Does not meet rubric |
|---|---:|---:|---:|---:|
| missing-structure | 9 | 3 | 4 | 2 |
| repeated-proof-machinery | 29 | 16 | 11 | 2 |

- **pursue**: A source-supported, worthwhile improvement candidate that I would pursue; exact replacement uncompiled.
- **qualified**: A plausible API/refactoring idea, but the revised rubric or the complete proposal is not established.
- **does_not_meet_rubric**: I would not accept this finding under the revised rubric, for the specific reason given.

Missing-structure has three concrete candidates: weight-linearity for additiveFunction, a public bivariate evaluation homomorphism, and the normal-disc family of linear isometries. Optional packaging and already-available structure still account for much of the remaining output.

Repeated-machinery identifies several substantial arguments worth sharing. Other findings are short API conveniences that do not clearly meet the substantial-argument requirement. Some polynomial findings overlap within one presentation/evaluation refactor; the number of findings is not a count of independent changes.

I would retain both rubrics as sources of candidates requiring review. These findings do not support treating every positive judgment as an established defect. No rubric or raw result was changed by this review.

## missing-structure

### lean-pool: clm_indicator'_eq_additiveFunction / zero_mem_convexHull_of_best_approx (use of additiveFunction a S under negation and scaling by ε)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L152-L178) — **pursue**.

The weight-to-set-function operation is genuinely linear, and the target plus Pipeline repeatedly unfold sums to prove negation, subtraction and scaling identities. A single LinearMap preserves the useful additiveFunction name and gives those actual consumers map_neg, map_sub and map_smul. This is a concrete interface improvement. Bundling finite additivity in the set argument is a separate issue; the proposed LinearMap addresses linearity in the weights.

Additional inspected sources:

- [LeanPool/KaltonRoberts/Defs.lean:61](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/Defs.lean#L61)
- [LeanPool/KaltonRoberts/Pipeline.lean:131](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/Pipeline.lean#L131)
- [LeanPool/KaltonRoberts/Pipeline.lean:186](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/Pipeline.lean#L186)

### lean-pool: clm_indicator'_eq_additiveFunction

[lean-pool-file-0001 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L70-L75) — **qualified**.

A name for the weight vector could clarify the proof, but a linear bundle in the functional is not shown to be needed. The proof already names the negated vector a, and the cited repeats include the statement and its immediate application rather than several independent consumers. The useful direction is optional naming or the first finding's weight-linearity API; this is not a convincing independent missing-structure defect.

Additional inspected sources:

- [LeanPool/KaltonRoberts/DualCert.lean:71](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L71)
- [LeanPool/KaltonRoberts/DualCert.lean:152](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L152)

### lean-pool: sectorCurve (with sectorCurve_continuousOn, sectorCurve_closed, deriv_sectorCurve_seg1/2/3)

[lean-pool-file-0003 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L64-L70) — **qualified**.

PiecewiseC1Curve is a mathematically appropriate bundle, and the source supplies continuity, closedness and segment derivatives. However, derivative continuity off the partition still needs a proof, and the named toLoop/toPath uses are hypothetical rather than an existing sector-curve consumer. Current sector computations take raw parametrizations. This is a plausible API addition, but the revised rubric's concrete-consumer and net-benefit requirements are not demonstrated. Moving the private off-knot lemma upward is feasible; importing SectorCurveLemma directly would cycle.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean:31](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean#L31)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Bridges.lean:69](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Bridges.lean#L69)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean:45](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean#L45)

### lean-pool: planeCurveFrobeniusRelation

[lean-pool-file-0008 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L187-L191) — **qualified**.

The composite really is a ring homomorphism, and naming it would remove one inline reconstruction in the evaluation proof. The broader benefits are overstated: degree formulas still need their mathematical proofs, and an injective ring homomorphism does not in general preserve irreducibility. The existing irreducibility proof correctly assumes irreducibility after coefficient extension and then uses an equivalence, in one line. A named composite is optional API; the finding does not establish a substantial cost from its absence.

Additional inspected sources:

- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean:227](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L227)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean:262](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L262)

### lean-pool: evalBivariate_planeCurveFrobeniusRelation (use of unbundled evalBivariate)

[lean-pool-file-0008 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L227-L233) — **pursue**.

A public two-stage evaluation RingHom in AuxiliaryFamily would serve actual consumers: BivariateResultant separately proves private add/mul lemmas, and the target and PlaneConstantField reconstruct evaluation homomorphisms. This is a concrete reason to expose the bundle while retaining evalBivariate. The proposed direct reuse of PlaneConstantField requires relocation: that file already depends transitively on the target. Move the generic evaluation interface and composition lemma to a lower layer rather than importing it back.

Additional inspected sources:

- [LeanPool/MarkoffModP/BGS/CorvajaZannier/AuxiliaryFamily.lean:84](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/AuxiliaryFamily.lean#L84)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/BivariateResultant.lean:61](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/BivariateResultant.lean#L61)
- [LeanPool/MarkoffModP/BGS/HasseWeil/PlaneConstantField.lean:36](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/HasseWeil/PlaneConstantField.lean#L36)

### mathlib: Algebra.TensorProduct.basisAux (with basisAux_map_smul and basis)

[mathlib-file-0004 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L46-L51) — **does_not_meet_rubric**.

The A-linear equivalence is already publicly exposed as (Algebra.TensorProduct.basis A b).repr. Replacing the internal R-linear construction and its smul proof with the existing heterobasic tensor/Finsupp equivalences looks like a reasonable implementation refactor, but it does not supply an unavailable structured interface. The revised rubric explicitly excludes structure already exposed by a public object. I would not count this as a missing-structure finding.

Additional inspected sources:

- [Mathlib/RingTheory/TensorProduct/Free.lean:65](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L65)
- [Mathlib/LinearAlgebra/DirectSum/Finsupp.lean:157](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/DirectSum/Finsupp.lean#L157)
- [Mathlib/LinearAlgebra/TensorProduct/Tower.lean:321](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/TensorProduct/Tower.lean#L321)

### mathlib: bijective_rootsOfUnityAddChar

[mathlib-file-0009 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L150-L154) — **does_not_meet_rubric**.

An equivalence is natural possible additional API, but no current consumer needing its inverse is identified. The suggested simplification of the existing bijectivity argument is circular: bijective_rootsOfUnityAddChar obtains surjectivity from the preceding composite-surjectivity theorem, so an equivalence built from that bijectivity cannot then replace the argument establishing it. The inverse/transport use cases remain hypothetical. I would not flag the present API under this rubric.

Additional inspected sources:

- [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean:145](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L145)
- [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean:150](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L150)

### tauceti: LinearMap.taylorComponent (with taylorComponent_zero, taylorComponent_add, taylorComponent_smul)

[tauceti-file-0001 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L516-L557) — **qualified**.

The outer map is indeed linear, and a bundled version can be constructed. But the preservation lemmas are already short simp lemmas, the cited AInfinity consumer needs only taylorComponent_zero, and no actual map_sum or kernel consumer is shown. The related coderivation-to-Taylor correspondence is itself already a LinearEquiv. This is optional further packaging, not an established practical deficiency in the current interface.

Additional inspected sources:

- [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean:485](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L485)
- [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean:532](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L532)
- [TauCeti/Algebra/Homology/AInfinity/Coderivation.lean:508](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/AInfinity/Coderivation.lean#L508)

### tauceti: TauCeti.exists_normalDisc

[tauceti-file-0007 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L324-L331) — **pursue**.

The construction is explicitly real-linear and norm-preserving, matching its docstring's description as a family of linear isometries. Returning LinearIsometries would expose that mathematics and supply norm_map, map_zero and injective to the existing solid-torus consumer. It also removes the separate injectivity proof from the existential interface. The continuity and range assertions still need to be retained, and the additional linearity fields need checking in an implementation.

Additional inspected sources:

- [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean:327](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L327)
- [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean:364](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L364)


## repeated-proof-machinery

### lean-pool: zero_mem_convexHull_of_best_approx (h_active, positive and negative branches)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L189-L248) — **pursue**.

The two long sign branches prove the same scalar perturbation fact with duplicated sum expansions. The proposed scalar lemma has sufficient hypotheses: |c| = M and c*x > 0 ensure that sufficiently small positive steps move c toward zero. Isolating that argument and using the sum-scaling identity once would remove substantial proof text and expose the reason the perturbation works. This is a strong candidate, though the replacement is uncompiled.

Additional inspected sources:

- [LeanPool/KaltonRoberts/DualCert.lean:187](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L187)

### lean-pool: dual_cert_from_convexHull (h_sum_eq, the two mirrored rcases branches)

[lean-pool-file-0001 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L395-L435) — **does_not_meet_rubric**.

The mirrored blocks are real, but the main proposed activeGenerators_decompose lemma restates the local h_sum_eq already being proved. Moving that whole proof to a named lemma leaves the two mirrored branches inside it. The alternative sign-parametrized abstraction is not given a precise statement or checked applications. Shared indicator-disjointness facts may help, but the finding has not demonstrated the net deduplication required by the revised rubric.

Additional inspected sources:

- [LeanPool/KaltonRoberts/DualCert.lean:376](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L376)
- [LeanPool/KaltonRoberts/DualCert.lean:394](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L394)

### lean-pool: realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree (and the same pattern in other files)

[lean-pool-file-0002 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384-L424) — **qualified**.

The representative conversion is genuinely repeated at the cited sites, and offering the commonly consumed representative form is sensible API design. However, the repeated portion is a short application of an existing a.e.-congruence lemma; the Fourier-to-divergence-free mathematical argument is already shared. I would treat this as an optional interface cleanup rather than substantial repeated proof machinery.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:384](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierHeatDivergence.lean:82](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierHeatDivergence.lean#L82)
- [LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedSolutionJ.lean:132](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedSolutionJ.lean#L132)

### lean-pool: realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree

[lean-pool-file-0002 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364-L413) — **qualified**.

Named Fourier-transform identities for the defined operators would be useful computational API. The shared proof, however, is apply_symm_apply plus routine transport of an a.e. equality; it is already an application of generic equivalence and Lp APIs. The finding does not establish a substantial repeated mathematical argument. I would consider the API lemmas during an ordinary cleanup without counting this as a clear rubric violation.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:364](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364)
- [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean:394](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L394)
- [LeanPool/CaffarelliKohnNirenberg/Leray/RegularisedBesselStokesPhysical.lean:222](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/RegularisedBesselStokesPhysical.lean#L222)

### lean-pool: pv_cutoff_F_integrable_delta_1, pv_cutoff_F_integrable_1_2, pv_cutoff_F_integrable_2_3delta, pv_cutoff_integral_seg1_eq_inv, pv_cutoff_integral_seg2_eq_Ialpha, pv_cutoff_integral_seg3_eq_neg_inv

[lean-pool-file-0003 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L342-L441) — **pursue**.

The same three segment formulas, including cutoff inequalities and field calculations, are re-proved for integrability and for integral evaluation, and again in SectorCurveLemma. Separate pointwise cutoff-integrand lemmas have exactly the shared mathematical content needed by those consumers. Their open-interval hypotheses match the actual uses. This is substantial duplication with a clear extraction, not merely similar tactics.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:358](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:504](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L504)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean:349](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean#L349)

### lean-pool: pv_cutoff_F_integrable_0_delta, pv_cutoff_F_integrable_3delta_3, pv_sector_cutoff_eq (hI1, hI5)

[lean-pool-file-0003 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593-L610) — **pursue**.

The endpoint cutoff-vanishing estimates recur independently in integrability and integral-zero proofs, and in SectorCurveLemma. Two pointwise zero lemmas on the stated closed endpoint intervals would cover all these uses, including the weaker Ioc restrictions. This is a concrete shared estimate and a clear reduction in repeated radius bookkeeping. It overlaps the preceding finding at the level of the overall cutoff-integrand refactor.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:307](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L307)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:593](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean:321](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean#L321)

### lean-pool: log_cancellation

[lean-pool-file-0003 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288-L297) — **pursue**.

The two existing integral lemmas have exactly the h1 and h2 statements after substituting ε/r. Both required inequalities are already proved in log_cancellation. Reusing them removes the repeated reciprocal-integral and change-of-variable arguments without adding any helper or assumptions. This is a direct, convincing reuse improvement.

Additional inspected sources:

- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:255](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L255)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:260](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L260)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean:288](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288)

### lean-pool: norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le

[lean-pool-file-0004 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428) — **qualified**.

The phase bound and Gaussian rearrangement repeat, and naming the polynomial majorant once would improve the second-derivative proof. But the principal Gaussian inequality is already shared as exp_neg_mul_sq_add_mul_le; much of the remaining repeated work is short algebra around different derivative estimates. The suggested helpers could tidy the code, but the claim that they remove the long common argument is stronger than the evidence. I would first try a small refactor and assess the complete diff.

Additional inspected sources:

- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:356](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L356)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:976](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L976)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:1108](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1108)

### lean-pool: poitouVerticalProfileDerivative_regularized_integrable (hone) vs integrable_quadratic_abs_mul_exp_neg_mul_sq

[lean-pool-file-0004 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L436-L449) — **pursue**.

The later quadratic Gaussian-integrability lemma directly includes the earlier linear majorant by setting C = 0. Moving that existing lemma earlier would remove the duplicated hzero/hone construction without creating another abstraction. The remaining measurability and majorization arguments remain specific to the derivative. The suggested specialization matches the actual assumptions.

Additional inspected sources:

- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:436](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L436)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:918](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L918)

### lean-pool: fourier_poitouVerticalProfileDerivative_regularized / fourier_poitouVerticalProfileSecondDerivative_regularized

[lean-pool-file-0004 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1180-L1210) — **qualified**.

A HasDerivAt form of the Fourier-derivative theorem is valid and could shorten both applications. The mathematical theorem is already shared as Real.fourier_deriv; the repeated part is conversion from a named derivative to deriv, application and simplification, made visually long by the function names. This is a reasonable convenience API proposal, but I do not regard substantial duplicated mathematics as established here.

Additional inspected sources:

- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:556](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L556)
- [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean:1180](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1180)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean:789`

### lean-pool: exists_positive_shell

[lean-pool-file-0005 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L128) — **pursue**.

The long logarithm/floor construction of a dyadic index is repeated in the parabolic near/far proofs and Euclidean Hedberg proofs. The cited Int.log bounds exist in the pinned Mathlib, and positivity of the ratio is available at the actual uses. A scalar radius-index lemma would isolate this substantial common estimate; the callers can supply their sign and Nat/Int conversions. Put the scalar lemma in a suitably shared lower layer rather than forcing Euclidean code to import parabolic machinery.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean:93](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean:178](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean#L178)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean:122](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean#L122)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/Data/Int/Log.lean:96`

### lean-pool: ennreal_mul_rpow

[lean-pool-file-0005 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L168-L190) — **pursue**.

This is especially clear: both long local proofs re-establish a product rpow identity already available as ENNReal.mul_rpow_of_ne_zero or ENNReal.mul_rpow_of_ne_top in the pinned Mathlib. The local hypotheses suffice for either route. Replacing the local helpers and updating their callers removes substantial proof text with no new abstraction.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean:168](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L168)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean:235](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean#L235)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean:738`

### lean-pool: positiveShell_pairwise

[lean-pool-file-0005 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L160) — **pursue**.

All four proofs use the same ordered-shell separation estimate, including mirrored order branches. Their indices are ordinary integers, natural casts, negative successors or fixed shifts, so a single disjointness theorem for integer-indexed shells covers them. The remaining injectivity/order translations are short. This is substantial common geometry with a precise natural statement.

Additional inspected sources:

- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean:138](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean:217](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean#L217)
- [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean:384](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean#L384)
- [LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedBase.lean:95](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedBase.lean#L95)

### lean-pool: RS.AnalyticAt.exists_taylor_remainder

[lean-pool-file-0006 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L195-L244) — **pursue**.

The Taylor remainder statements express the same factorization, with the RS statement additionally pointwise and coefficient-aware. Its specialization can replace the separate power-series tail calculation after bridging taylorCoeffAt to iterated derivatives. TaylorCoeff imports only Mathlib and neither file transitively imports the other in the inspected LeanPool graph, so sharing the result is feasible without the hypothesized cycle. The coefficient bridge and final replacement still need compilation.

Additional inspected sources:

- [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean:195](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L195)
- [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicPrincipalPart.lean:153](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicPrincipalPart.lean#L153)

### lean-pool: weakPathRepresentative_pairing_eq_inner / FrozenDriftProblem.initial_pairing_eq_cell_integral

[lean-pool-file-0007 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188-L263) — **pursue**.

The two calc blocks repeat the same nontrivial bridge from torus L2 inner products through a.e. representatives to unit-cell and unit-cube integrals. The proposed helper's two a.e. hypotheses fit both sites. I checked that the existing integral_periodicToTorus_eq_unitCell theorem applies to arbitrary functions, so the helper is not missing an extra periodicity assumption. This would make both proofs state only their particular representative equalities.

Additional inspected sources:

- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:188](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188)
- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:230](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L230)
- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean:195](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean#L195)

### lean-pool: weakPathRepresentative_isPeriodic / weakPathRepresentative_memL2On / weakPathRepresentative_l2NormSq / weakPathRepresentative_pairing_eq_inner

[lean-pool-file-0007 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184) — **does_not_meet_rubric**.

The four unfolds really repeat, and an evaluation lemma would be a sensible small API cleanup. However, each is a short simplification of the same conditional definition. This is exactly the routine computation excluded by the revised substantial-argument requirement. Repetition at four sites alone does not establish the requested mathematical machinery defect.

Additional inspected sources:

- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:153](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L153)
- [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean:168](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168)

### lean-pool: bivariateEquiv_symm_natDegree_eq_degreeOf_one

[lean-pool-file-0008 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L134-L169) — **pursue**.

The already-proved presentation identity and degree formula do give the target theorem, avoiding its long optionEquivLeft/ringHom_ext reconstruction. Directly importing PlaneCurveLocalReciprocalDiscriminant would cycle through the target; the proposed relocation into PlaneCurveDiscriminantBound resolves that dependency direction. This is a credible reuse/refactoring candidate, with the necessary supporting generator facts moved together.

Additional inspected sources:

- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean:136](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L136)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveDiscriminantBound.lean:158](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveDiscriminantBound.lean#L158)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean:98](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean#L98)

### lean-pool: planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C

[lean-pool-file-0008 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L50-L99) — **pursue**.

The generator computations are genuinely repeated for the same finSuccEquiv/uniqueAlgEquiv construction, with a coordinate swap in one presentation. Moving the common presentation and generator API lower would let the swapped case use them directly. The pinned Mathlib also already exposes finSuccEquiv_X_zero and finSuccEquiv_X_succ, so those internal computations should not be re-proved. This overlaps the preceding polynomial-presentation refactor; the claimed line saving needs an actual diff.

Additional inspected sources:

- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean:50](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L50)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean:40](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean#L40)
- `repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean:681`

### lean-pool: evalBivariate_planeCurveFrobeniusRelation

[lean-pool-file-0008 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L219-L259) — **pursue**.

The evaluation comparison is re-proved by ring-hom extensionality and the same generator checks. A generic evaluation lemma for the source-oriented presentation, with the actual coefficient map/tower identity, covers the Frobenius case. The orientation in the proposed formula is correct. Existing related generic lemmas live downstream, including PlaneConstantField, so factor the common theorem into a lower module. This is a meaningful repeated argument, overlapping the missing evaluation-interface finding.

Additional inspected sources:

- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean:219](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L219)
- [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean:113](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean#L113)
- [LeanPool/MarkoffModP/BGS/HasseWeil/PlaneConstantField.lean:36](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/HasseWeil/PlaneConstantField.lean#L36)

### lean-pool: EulerMeanHarmonic.localL2Energy_ball_le_of_ae_bound

[lean-pool-file-0009 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L79-L88) — **qualified**.

The proposed constant-bound integral helper is valid and fits both real-valued integrands; the harmonic pointwise bound can supply its a.e. premise. However, the shared argument is already just integral monotonicity, the constant-integral formula and the shared volume_ball_toReal lemma. This is an optional short convenience lemma rather than a convincing instance of substantial repeated machinery.

Additional inspected sources:

- [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean:76](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L76)
- [LeanPool/NavierStokesAndEuler/Euler/MeanHarmonicSmallBall.lean:39](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanHarmonicSmallBall.lean#L39)

### mathlib: Profinite.effectiveEpiFamily_tfae

[mathlib-file-0002 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L86-L90) — **qualified**.

The Profinite and Stonean transfer blocks are visibly identical except for their functors. Nevertheless, the proposed abstraction does not specify the exact concrete-category and effective-epi assumptions, and explicitly leaves them unchecked. The repeated block is fairly short and already uses general transfer API. A precise generic statement and complete diff are needed before concluding the extra infrastructure improves the code.

Additional inspected sources:

- [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean:74](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L74)
- [Mathlib/Topology/Category/Stonean/EffectiveEpi.lean:74](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Stonean/EffectiveEpi.lean#L74)

### mathlib: Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow

[mathlib-file-0003 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293) — **qualified**.

The proposed real-variable estimate and composition with the natural cast are mathematically sound and fit the two uses. But the shared estimate is only a few straightforward calculation steps, and a new helper has statement and naming costs. This is a reasonable optional refactor; it does not clearly satisfy the revised requirement for substantial repeated machinery.

Additional inspected sources:

- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:274](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274)
- [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:284](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L284)

### mathlib: Bundle.Trivialization.mk_coordChangeL and VectorPrebundle.mk_coordChange

[mathlib-file-0006 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L324) — **qualified**.

The first-component proof is repeated and can be shortened using existing mk_proj_snd or mk_proj_snd' API; the Trivialization case also has the cited general coordinate-change lemma. The proposed new first-component helper is therefore unnecessary. This is a small proof/API-use cleanup, not a substantial repeated mathematical argument.

Additional inspected sources:

- [Mathlib/Topology/VectorBundle/Basic.lean:316](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316)
- [Mathlib/Topology/VectorBundle/Basic.lean:858](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L858)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:125](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L125)
- [Mathlib/Topology/FiberBundle/Trivialization.lean:756](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/FiberBundle/Trivialization.lean#L756)

### tauceti: TauCeti.ReducedTensorWords.letter_comp_coderiv

[tauceti-file-0001 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L433-L451) — **pursue**.

The double-sum whole-word projection proof is repeated between graded and ungraded coderivations. The proposed family-of-tuples helper is sufficient: non-whole splices vanish for arbitrary tuples, and the surviving whole splice returns its inserted coefficient independently of the tuple. Thus no compatibility condition between different y p values is needed. This isolates a coherent combinatorial lemma and leaves both consumers with short applications.

Additional inspected sources:

- [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean:413](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L413)
- [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean:433](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L433)
- [TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean:889](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean#L889)

### tauceti: TauCeti.schwarzChristoffelBoundary_injOn (also collinear_schwarzChristoffelBoundary_image, schwarzChristoffelBoundary_sub_eq, continuousOn_schwarzChristoffelBoundary)

[tauceti-file-0004 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L225-L233) — **qualified**.

The repeated transfer from an auxiliary limit function to the canonical boundary is real, and an EqOn lemma or direct boundary formulation could shorten the image proof. But the first proposed Tendsto lemma alone does not remove the comparisons with each existential L, while the stronger proposed interface leaves its conclusions unspecified. The uniqueness-of-limit argument is already shared by schwarzChristoffelBoundary_eq_of_tendsto. A coherent cleanup is plausible, but the precise shared abstraction and net gain required by the rubric are not demonstrated.

Additional inspected sources:

- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean:167](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L167)
- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean:225](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L225)
- [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean:451](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean#L451)

### tauceti: TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg

[tauceti-file-0005 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L96-L102) — **pursue**.

The root-sum bookkeeping followed by cyclic Killing symmetry and skew symmetry is repeated in Opposite and Normalization. The proposed Chevalley-free weighted identity is a natural mathematical intermediate, applies to both calculations, and belongs in their already-common Symmetry dependency. It would distinguish the shared symmetry argument from the later Chevalley-involution and root-length inputs. This is worth implementing and checking.

Additional inspected sources:

- [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean:93](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L93)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean:98](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean#L98)
- [TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean)

### tauceti: TauCeti.exists_forall_notMem_span_tangentVector (private)

[tauceti-file-0007 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L264-L278) — **qualified**.

The cone-over-a-curve observation is valid and common to both proofs. However, its proof is only the three-step construction of F, its differentiability, and application of the existing dimension/range theorem; most of each proof is distinct input or conclusion bookkeeping. A named cone lemma is plausible API, but the finding has not demonstrated a net improvement after its full statement, ambient hypotheses and calls are counted.

Additional inspected sources:

- [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean:264](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L264)
- [TauCeti/Geometry/Manifold/Instances/Sphere.lean:280](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Manifold/Instances/Sphere.lean#L280)

### tauceti: TauCeti.orbitRank_rigidSixGraph

[tauceti-file-0008 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L128-L140) — **pursue**.

The proposed rank-jump criterion is mathematically sufficient: stability at γ+1 supplies the upper bound, while a pair equivalent at γ but separated at γ+1 rules out stability at γ and hence orbitRank ≤ γ. Both graph examples have exactly that witness structure. Naming this rank criterion moves the ordinal/rank reasoning into Rank and leaves the examples focused on graph-specific separation. The repeated block is modest, but the shared statement has a clear mathematical role and concrete uses.

Additional inspected sources:

- [TauCeti/ModelTheory/Scott/RigidGraph.lean:128](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L128)
- [TauCeti/ModelTheory/Scott/CompleteGraphSum.lean:163](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/CompleteGraphSum.lean#L163)
- [TauCeti/ModelTheory/Scott/Rank.lean:102](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/Rank.lean#L102)

### tauceti: TauCeti.two_mem_orbitStable_rigidSixGraph

[tauceti-file-0008 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L114-L125) — **qualified**.

The proposed orbit-stability lemma follows correctly from the existing automorphism-to-BF-equivalence API, and the three cited consumers fit it. But the common proof is just unfolding orbitStable, obtaining the automorphism and applying σ.bfEquiv. Those few routine steps are already very short. This is optional convenience API, not compelling substantial repeated machinery under the revised rubric.

Additional inspected sources:

- [TauCeti/ModelTheory/Scott/RigidGraph.lean:114](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L114)
- [TauCeti/ModelTheory/Scott/CompleteGraphSum.lean:154](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/CompleteGraphSum.lean#L154)
- [TauCeti/ModelTheory/Scott/Finite.lean:99](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/Finite.lean#L99)
