# Review of three file-audit rubrics

Every positive Sonnet finding was reviewed: 11 missing-structure, 59 fragile-proofs, and 31 repeated-proof-machinery findings (101 total). These assessments were explicitly requested; original judgments are unchanged.

The review inspected target source and relevant cited APIs/proof blocks. It did not compile proposed replacements, validate every candidate helper statement, or perform robustness perturbation tests. Useful candidate means a source-supported improvement worth testing, not a confirmed defect or an accuracy estimate.

| Rubric | Findings | Useful candidates | Optional refactors | Not established / outside scope / incomplete proposal | Recommendation |
|---|---:|---:|---:|---:|---|
| missing-structure | 11 | 3 | 5 | 3 | revise |
| fragile-proofs | 59 | 13 | 22 | 24 | drop as a separate judge-only quality score for now |
| repeated-proof-machinery | 31 | 17 | 10 | 4 | revise, retain the experiment |

The existing missing-structure rubric already requires an actual benefit and checking for an existing bundle; repeated-proof-machinery already excludes short proofs and asks for a precise helper. Several judgments fail those requirements. The proposed wording below sharpens the evidence required, but a small rerun is needed to learn whether the judge follows it better. These recommendations do not establish that a prompt revision will fix the experiment.

## missing-structure

There are genuine bundling opportunities, but the rubric admits generic implementation reuse, already-available structure and hypothetical consumers.

Find a map or mathematical object whose useful algebraic, topological or inverse structure is exposed only as separate facts. Identify the standard bundle, explain how its fields are supplied, and show an actual consumer that benefits. Do not count structure already available through an existing public object, implementation via a generic combinator, or unused hypothetical API. Preserve useful names and account for the cost of bundling.

### lean-pool: zero_mem_convexHull_of_best_approx (use of additiveFunction with scaled/negated weights)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L153-L178) — **useful_candidate**.

The weight-to-set-function operation is genuinely linear, and negation/scaling/addition algebra is repeated in this proof and Pipeline. A bundled LinearMap or a shared preservation API has concrete consumers; the exact implementation remains uncompiled.

### lean-pool: clm_decompose / clm_indicator'_eq_additiveFunction

[lean-pool-file-0001 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L52-L75) — **outside_rubric**.

This proposes using Pi.single and an existing coordinate-expansion theorem. That is a proof/API reuse improvement, not a missing homomorphism or equivalence.

### lean-pool: l2BasisVec (with l2BasisVec_norm, inner_l2BasisVec, gradientOfCovectorLinear, gradientOfCovectorLinear_norm_bound)

[lean-pool-file-0002 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L44-L62) — **optional_refactor**.

An OrthonormalBasis is available and could provide useful extra API, but the named specialised basis vectors are defensible and the cited norm/inner lemmas are already short simp proofs. The finding does not demonstrate a substantial cost from the current interface.

### lean-pool: evalBivariate_planeCurveFrobeniusRelation

[lean-pool-file-0008 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L219-L257) — **useful_candidate**.

The target rebuilds evaluation as a local RingHom, and another project file already exposes the corresponding AlgHom. Making that structured evaluation available at the correct dependency level is a concrete integration opportunity; import direction and the exact migration need checking.

### lean-pool: planeCurveFrobeniusRelation

[lean-pool-file-0008 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L187-L192) — **optional_refactor**.

The composite does preserve ring operations, so bundling is possible. However, the cited degree/irreducibility/evaluation facts do not follow merely from map_add/map_mul, and no actual later product/power use is identified. The claimed benefit needs a stronger consumer example.

### mathlib: DFinsupp.singleton

[mathlib-file-0001 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L86) — **outside_rubric**.

DFinsupp.singleton is already a bundled DFinsupp. Using mapRange changes its implementation; it does not supply missing mathematical structure. A useful named API should remain.

### mathlib: DFinsupp.rangeIcc

[mathlib-file-0001 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L98-L109) — **outside_rubric**.

DFinsupp.rangeIcc already returns a DFinsupp. Reusing zipWith is an implementation refactor rather than exposure of a missing homomorphism, equivalence or similar interface.

### mathlib: Algebra.TensorProduct.basisAux / basisAux_map_smul / basis

[mathlib-file-0004 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L45-L66) — **optional_refactor**.

The A-linear equivalence is already exposed as (Algebra.TensorProduct.basis A b).repr. Making basisAux A-linear may tidy internal construction, but the claim that the natural structured object is unavailable is overstated.

### mathlib: ZMod.rootsOfUnityAddChar / bijective_rootsOfUnityAddChar / surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar

[mathlib-file-0009 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L145-L154) — **optional_refactor**.

The bijective AddChar can be packaged as an equivalence after the appropriate Additive/Multiplicative conversion. That is natural additional API, but the finding supplies no existing consumer needing its inverse or transport, so it is an opportunity rather than an established defect.

### tauceti: LinearMap.taylorComponent (with taylorComponent_zero / taylorComponent_add / taylorComponent_smul)

[tauceti-file-0001 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L513-L556) — **optional_refactor**.

Linearity in the endomorphism is real, but each arity component already returns a LinearMap. The outer zero/add/smul lemmas are short and the cited consumers primarily need zero/evaluation. Bundling the outer map is plausible additional API; the current practical cost is not convincingly established.

### tauceti: TauCeti.exists_normalDisc

[tauceti-file-0007 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L324-L331) — **useful_candidate**.

The private theorem constructs an explicitly real-linear, norm-preserving normal-disc map but returns a bare function with separate norm/injectivity facts. Its actual consumer projects and uses both properties. A family of LinearIsometries would state the documented mathematics and supply those operations directly; construction cost and elaboration still need testing.


## fragile-proofs

Most findings infer fragility from ordinary simp, rfl, case analysis, coercions or potential API changes. Some concrete improvements are useful, but overlap proof simplification and do not validate a reliable source-only fragility measure.

Route specific simplifications to the readability audit. A future robustness experiment should define a controlled semantics-preserving perturbation, reproduce a failure, and check that the proposed repair survives it.

### lean-pool: zero_mem_convexHull_of_best_approx (h_active branches)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L191-L248) — **useful_candidate**.

Long nonterminal context simplification is followed by an explicit epsilon witness whose shape depends on expanded sums. Naming the scalar coefficient and stating its scaling law would isolate a concrete source of context-sensitive elaboration.

### lean-pool: zero_mem_convexHull_of_best_approx (Hahn–Banach application)

[lean-pool-file-0001 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L136-L137) — **not_established**.

The expression first binds @geometric_hahn_banach_closed_point and then applies the local theorem normally. Sonnet treats this as if every implicit argument were passed positionally at the later call; that is not established. Direct application could simplify the proof, but the stated fragility claim is overstated.

### lean-pool: dual_cert_from_convexHull (h_sum_eq block)

[lean-pool-file-0001 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L394-L435) — **optional_refactor**.

The two sum branches are intricate and could benefit from shared indicator facts. Expected side goals of sum_eq_single are not incidental merely because bullets discharge them. The strongest supported diagnosis is repeated machinery.

### lean-pool: dual_cert_from_convexHull (lam_pos/lam_neg construction)

[lean-pool-file-0001 finding 3](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L314-L376) — **optional_refactor**.

Named intermediate properties could help navigate the long weight construction. The finding otherwise largely equates tactic-generated side goals and conjunction projections with fragility, without a demonstrated maintenance failure.

### lean-pool: zero_mem_convexHull_of_best_approx (h_inactive continuity step)

[lean-pool-file-0001 finding 4](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L174-L178) — **not_established**.

Replacing the terminal continuity tactic by fun_prop is not evidence of reduced fragility. Both are legitimate public automation interfaces; no failing rule dependency is identified.

### lean-pool: realPart_isWeakDivFree_of_fourierOrthogonal (hpoint)

[lean-pool-file-0002 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L299-L300) — **useful_candidate**.

The proof unfolds mkContinuous and multiple structure projections in several consumer files. A coordinate apply lemma would give those consumers a genuine stable boundary instead of reconstructing the implementation.

### lean-pool: weakTestGradientSchwartz_apply

[lean-pool-file-0002 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L173-L189) — **optional_refactor**.

Several apply lemmas may shorten wrapper computations, but the proof is a chain-rule calculation and some local definitions necessarily enter it. The complete proposed route has not been verified.

### lean-pool: realPart_isWeakDivFree_of_fourierOrthogonal (pointwise comparison step)

[lean-pool-file-0002 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L320-L325) — **optional_refactor**.

A coordinate evaluation lemma could clarify this representation bridge. The source must still relate the chosen coordinate equivalence and WithLp representation, so an arbitrary change to them is not automatically a robustness defect.

### lean-pool: integral_seg1_eq_neg_log / integral_seg3_eq_log (and the `h2` step in log_cancellation)

[lean-pool-file-0003 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L255-L268) — **not_established**.

The simplifications are terminal and express elementary integral/log identities. Their reliance on the simp set is not enough to establish a specific defect.

### lean-pool: pv_cutoff_F_integrable_delta_1 (same pattern in the other pv_cutoff_* lemmas and in pv_sector_cutoff_eq, lines 319, 336, 359, 382, 414, 505, 528, 559, 597, 606)

[lean-pool-file-0003 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358-L363) — **not_established**.

The side-condition order of ite_eq_left and ite_eq_right follows their theorem statements. Display notation changes between greater-than and less-than are not substantive changes to those conditions; moving the proof to a named hypothesis is a presentation option.

### lean-pool: pv_sector_dz_over_z

[lean-pool-file-0003 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L648-L650) — **optional_refactor**.

A general principal-value-equals-limit lemma might be useful API. The current two-line proof is also the natural immediate consequence of the definition, and no actual breakage is shown.

### lean-pool: fourier_poitouVerticalProfileDerivative_regularized (also fourier_poitouVerticalProfileSecondDerivative_regularized)

[lean-pool-file-0004 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L570-L579) — **optional_refactor**.

A typed simpa only using the derivative identity may make the final use clearer, but the current terminal simp_all is not independently shown fragile.

### lean-pool: sq_abs_mul_norm_poitouTransform_regularized_le (hfactor/hnorm)

[lean-pool-file-0004 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1238-L1251) — **useful_candidate**.

The norm calculation uses nonterminal norm_num followed by field_simp and simp; stronger normalisation can invalidate later tactics. A targeted explicit norm identity is a concrete robustness candidate; the suggested replacement remains uncompiled.

### lean-pool: norm_poitouVerticalProfileDerivative_regularized_le and norm_poitouVerticalProfileSecondDerivative_regularized_le (norm computation steps)

[lean-pool-file-0004 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L384-L392) — **useful_candidate**.

The source runs nonterminal norm_num before rewriting a specific remaining norm expression. That is a concrete pattern-sensitive dependency, though the exact repair needs elaboration and regression checks.

### lean-pool: poitouVerticalProfileDerivative_regularized_integrable and integrable_quadratic_abs_mul_exp_neg_mul_sq (hone/htwo)

[lean-pool-file-0004 finding 3](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L926-L937) — **optional_refactor**.

Explicit Integrable.congr could expose the pointwise norm identity. The present terminal simp_all is also reasonable, and no actual bad normal form is exhibited.

### lean-pool: abs_sinh_le_cosh

[lean-pool-file-0004 finding 4](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L202-L207) — **not_established**.

The one-line terminal simp_all simply applies sq_abs in the current context. Its existence is not evidence of fragility, and the proposed whole-proof replacement cites unchecked alternative names.

### lean-pool: CKN.Foundation.Parabolic.Morrey.cylinderAbsIntegral_le_morreyNorm

[lean-pool-file-0005 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L61-L65) — **not_established**.

Commutative simp is a standard way to align multiplication sides. Its ordered rewriting avoids the alleged automatic looping; choosing the other monotonicity lemma is a small simplification, not established fragility.

### lean-pool: CKN.Foundation.Parabolic.Morrey.positive_shell_integral_le (hprod)

[lean-pool-file-0005 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L227-L229) — **not_established**.

The proof uses terminal simpa [mul_comm] to align an inequality. Sonnet has not shown that this is unstable or that a mathematical API renaming is an avoidable dependency.

### lean-pool: CKN.Foundation.Parabolic.Morrey.positive_shell_integral_le (final calc step)

[lean-pool-file-0005 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L265-L267) — **not_established**.

Associative/commutative simp normalises both sides together. Different canonical ordering does not itself make this proof fail; the proposed direct monotonicity application is optional cleanup.

### lean-pool: RS.taylorCoeffAt_add

[lean-pool-file-0006 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L122-L127) — **not_established**.

Reflexivity of coefficient addition is appropriate for pointwise-defined formal series. Replacing rfl by unfolding coeff plus add_apply still depends on that same representation and does not establish a robustness improvement.

### lean-pool: scalarTorusRepresentative_memL2On (local `hequiv`)

[lean-pool-file-0007 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L102-L107) — **optional_refactor**.

The cited public measurable-equivalence computation lemma does exist and may shorten the proof. Its current inverse/projection calculation is also conventional; the risk claim remains hypothetical.

### lean-pool: scalarTorusRepresentative_memL2On (`hmeasureTorus`)

[lean-pool-file-0007 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L93-L96) — **not_established**.

This deliberately bridges the project cell definition to the standard Ioc cell using simp. Normalising zero plus one is appropriate and does not constitute a demonstrated defect.

### lean-pool: weakPathRepresentative_pairing_eq_inner and FrozenDriftProblem.initial_pairing_eq_cell_integral

[lean-pool-file-0007 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L217-L221) — **optional_refactor**.

A multiplicativity lemma for periodicToTorus would avoid repeating long rfl expressions. That is a useful small API/repetition suggestion, not independently established fragility.

### lean-pool: planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C

[lean-pool-file-0008 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L51-L100) — **useful_candidate**.

The pinned Mathlib supplies finSuccEquiv_X_zero and finSuccEquiv_X_succ, while these proofs expand the equivalence and inspect its finite-index implementation. Reusing the public generator rules removes a specific low-level dependency.

### lean-pool: bivariateEquiv_symm_natDegree_eq_degreeOf_one

[lean-pool-file-0008 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L135-L170) — **not_established**.

The proposed degree argument itself requires an unprovided degree-under-transposition theorem. The existing ring-hom comparison is legitimate; no verified simpler stable replacement is demonstrated.

### lean-pool: EulerMeanHarmonic.localL2Energy_ball_le_of_ae_bound

[lean-pool-file-0009 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L85-L87) — **not_established**.

Changing Measure.real to toReal is a short intentional representation bridge. The alternative named rewrite has similar content and no concrete instability is shown.

### mathlib: DFinsupp.card_pi

[mathlib-file-0001 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L140-L142) — **useful_candidate**.

The prod argument is missing its value binder and relies on a Nat-to-function coercion, as confirmed by Pi.natCast_apply in the proof and the prod signature. Writing fun i s => #s removes a concrete elaboration dependency and clarifies the statement.

### mathlib: Finset.mem_dfinsupp_iff

[mathlib-file-0001 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L48-L59) — **optional_refactor**.

A public mk-of-mem/not-mem proof may avoid unfolding, but the present short proof is an immediate constructor-membership theorem. Dependence on that constructor is not by itself evidence of unusual fragility.

### mathlib: Profinite.effectiveEpiFamily_tfae

[mathlib-file-0002 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L86-L90) — **optional_refactor**.

Replacing erw by explicit iff composition is plausible and may clarify the transfer. The replacement still relies on the functor coercions reducing appropriately, and no actual failure or robustly eliminated dependency is demonstrated.

### mathlib: Profinite.effectiveEpiFamily_tfae

[mathlib-file-0002 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L82-L84) — **not_established**.

This is a terminal simpa using explicitly supplied equivalences. A hypothetical new simp lemma or changed iff statement does not establish a defect, and a loop is not demonstrated.

### mathlib: tendsto_log_mul_self_nhdsLT_zero

[mathlib-file-0003 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L410-L415) — **useful_candidate**.

nth_rewrite 3 selects an otherwise unnamed occurrence of zero in a limit expression. This is a specific positional dependency; stating the desired limit explicitly is a reasonable maintenance improvement, though the proposed code was not compiled.

### mathlib: tendsto_rpow_atTop_of_base_lt_one

[mathlib-file-0003 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L53-L76) — **not_established**.

The case labels follow the standard nested disjunction of lt_trichotomy. The claimed conflict with nested exp/cos goals is not shown. A changed theorem statement would also affect positional rcases/bullets.

### mathlib: Algebra.TensorProduct.basis_repr_symm_apply

[mathlib-file-0004 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L73-L75) — **useful_candidate**.

The inverse-basis formula unfolds several constructor equivalences although the immediately preceding forward repr-on-tensor lemma provides a public route. This is a concrete opportunity to isolate implementation dependence; the exact replacement is uncompiled.

### mathlib: CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci

[mathlib-file-0005 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L101-L103) — **useful_candidate**.

IsSuccLimit has a named not_isMin field. Replacing hm.1 with hm.not_isMin avoids an unnecessary numeric field selector and improves intent at essentially no cost.

### mathlib: CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci

[mathlib-file-0005 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L90-L96) — **not_established**.

Pattern matching on nested subtypes and reducing a local function are ordinary proof techniques. Replacing them by projections still depends on the same subtype structure, so the suggested stability gain is not established.

### mathlib: VectorBundleCore.localTriv_continuousLinearMapAt

[mathlib-file-0006 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L768-L772) — **useful_candidate**.

Nonterminal simp_all followed by rfl creates a specific no-goals risk if simplification becomes stronger. The existing continuousLinearMapAt_apply_of_mem lemma gives a more controlled route.

### mathlib: VectorPrebundle.toVectorBundle

[mathlib-file-0006 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L939-L944) — **optional_refactor**.

A lemma stated for the exact wrapper term could simplify instance transport. The current source is itself implementing that wrapper, so unfolding it is not automatically inappropriate and the alternative needs elaboration checks.

### mathlib: Bundle.Trivialization.continuousLinearEquivAt

[mathlib-file-0006 finding 2](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L456-L456) — **optional_refactor**.

Continuous.congr with symmL_apply looks clearer than convert/ext/simp. This is a small proof simplification, without evidence that the existing short proof is unusually fragile.

### mathlib: Equiv.lawfulFunctor'

[mathlib-file-0007 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L78-L83) — **optional_refactor**.

The proof does depend on the fields of Functor while proving equality of Functor structures. A field-oriented proof may be easier to read, but changing those fields is a relevant API change and the proposed ext theorem is not established.

### mathlib: Equiv.isLawfulTraversable'

[mathlib-file-0007 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L169-L171) — **not_established**.

Rewriting an explicit traverse compatibility hypothesis is normal transport reasoning. The finding speculates about changes to Comp and congr without a demonstrated failure or a verified replacement.

### mathlib: CliffordAlgebra.contractLeft_ι_mul (also contractLeft_ι, contractLeft_algebraMap)

[mathlib-file-0008 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L123-L127) — **useful_candidate**.

Unlike most hypothetical claims, the source contains an actual porting note about failure to infer the foldr witness, alongside elaboration options. Centralising the fold application is worth testing; merely adding an apply lemma has not yet been shown to remove the underlying sensitivity.

### mathlib: CliffordAlgebra.changeForm_ι_mul

[mathlib-file-0008 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L279-L281) — **optional_refactor**.

Using a generated apply lemma can make the final step explicit, but reduction of the definition being analysed is also legitimate. The proposed change is a minor maintainability preference, not a demonstrated failure.

### mathlib: ZMod.toCircle_intCast

[mathlib-file-0009 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L53-L58) — **useful_candidate**.

The proof reaches through Periodic.lift_coe and AddChar structure projections, while the circle map exposes a value-on-cosets lemma. Using that public computation rule is a concrete way to reduce low-level dependencies.

### mathlib: rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val

[mathlib-file-0009 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L139-L143) — **optional_refactor**.

The existing projection/apply lemmas suggest a shorter direct calculation. The asserted simp loop is not shown; the supported part is proof simplification rather than an observed robustness defect.

### mathlib: bijective_rootsOfUnityAddChar

[mathlib-file-0009 finding 2](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L150-L152) — **optional_refactor**.

Injectivity can likely use the public value projection. The current one-line unfolding proof is also straightforward and no specific breakage is demonstrated.

### tauceti: TauCeti.gradedIdempotentHeadBasis

[tauceti-file-0000 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean#L51-L59) — **not_established**.

Classical decidability and terminal simpa on a Kronecker-delta formula are normal here. The suggested explicit if reductions preserve the same core dependencies and do not establish a practical robustness improvement.

### tauceti: TauCeti.ReducedTensorWords.isCoderivation_coderiv

[tauceti-file-0001 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L386-L399) — **optional_refactor**.

Naming the component sum equalities might clarify the long calculation. However, rewriting a top-level sum with add_comm and then proving its components is ordinary algebraic transport; no actual matching failure is established.

### tauceti: TauCeti.ReducedTensorWords.coderivSummand_tprod

[tauceti-file-0001 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L129-L147) — **optional_refactor**.

A Fin.append computation API could hide index representation details, but this is itself a low-level tensor computation proof. The alternative requires substantial new case reasoning and has not been demonstrated to improve net maintenance.

### tauceti: Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup (hoff: hli, hlj)

[tauceti-file-0003 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L50-L52) — **not_established**.

These two terminal simp_all calls derive inequalities from nonmembership of a two-element finset. Hypothetical unrelated context changes and a supposed generated name are insufficient evidence of fragility.

### tauceti: Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup (hdiag)

[tauceti-file-0003 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L70-L75) — **not_established**.

The calculation explicitly applies a commutation equation to coordinates and normalises matrix-vector products. The suggested intermediate statement repeats the same mathematical steps; changing the rotation theorem is an API change, not a demonstrated avoidable dependency.

### tauceti: TauCeti.hasDerivAt_schwarzChristoffelBoundary (hcast step)

[tauceti-file-0004 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L208-L211) — **not_established**.

The source uses a public continuous-linear-map chain rule. The proposed exact HasDerivAt.ofReal_comp name was not found in the pinned calculus sources. This does not establish a verified more stable alternative.

### tauceti: TauCeti.schwarzChristoffelBoundary_eq_of_tendsto and continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one (closure computations)

[tauceti-file-0004 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L90-L90) — **not_established**.

The proof names the current public closure lemma, not its deprecated alias. Replacing a named rewrite by simp does not in itself make a proof more robust; repeated use of a simple closure fact is not unusual fragility.

### tauceti: TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg (and structureConstant_neg_neg_eq_neg_iff)

[tauceti-file-0005 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L88-L90) — **optional_refactor**.

A shared negated-weight relation could reduce inline dependent-statement bookkeeping. The three coe_neg rewrites are nevertheless explicit mathematics, and the finding mainly identifies repetition rather than proven fragility.

### tauceti: TauCeti.NumberField.FifthCyclotomic.map_span_five_eq_pow_four

[tauceti-file-0006 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L137-L150) — **not_established**.

The local cyclotomic-extension fact is genuinely used through instance synthesis, so its implicit use is not a silent unused-hypothesis defect. Numeral and power rewrites are expected in this specialisation; the claimed linter/clear_unused failure is speculative.

### tauceti: TauCeti.exists_isSolidTorusNeighborhood (injectivity step `hinj`)

[tauceti-file-0007 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L372-L377) — **optional_refactor**.

An explicit intermediate subtype equality may clarify the embedding-injectivity argument. Named arguments of Injective and subtype/product destructuring are ordinary API use; their hypothetical renaming does not establish a defect.

### tauceti: TauCeti.exists_isSolidTorusNeighborhood (openness of the image, `convert ... using 1`)

[tauceti-file-0007 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L384-L400) — **not_established**.

The proposed named image equality contains the same nested subtype/set-image argument as the current convert block. It largely moves that argument without removing its dependencies.

### tauceti: TauCeti.exists_forall_notMem_span_tangentVector

[tauceti-file-0007 finding 2](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L269-L270) — **useful_candidate**.

The derivative regularity argument selects the third conjunct of a version-sensitive ContDiff characterisation. A direct derivative regularity API would isolate that dependency; a suitable exact replacement and its assumptions still need checking.

### tauceti: TauCeti.bfEquiv_two_rigidSixGraph_iff

[tauceti-file-0008 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L90-L96) — **optional_refactor**.

Naming forth/back would improve readability. Pattern destructuring still relies on the same conjunct order, so the proposed replacement does not establish added robustness.

### tauceti: TauCeti.orbitRank_rigidSixGraph

[tauceti-file-0008 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L132-L134) — **not_established**.

The short rewrite chain expresses the ordinal arithmetic and orbit-rank characterisation directly. A hypothetical restatement of those lemmas would also affect the proposed contradiction argument.


## repeated-proof-machinery

Substantial common arguments are visible in multiple libraries, especially cutoff integrals, Gaussian bounds, shell geometry and tensor combinatorics. Short proof patterns and speculative universal helpers should not receive the same finding.

Find a substantial mathematical argument repeated at two or more source locations. Give a precise shared lemma, or an existing lemma to reuse, and explain how it applies at every cited location under the actual assumptions and import dependencies. Show a net improvement including the helper statement/proof and all call sites. Common tactics, routine inductions, short case splits and moving repetition into a more complicated abstraction are insufficient.

### lean-pool: zero_mem_convexHull_of_best_approx (h_inactive / h_active inside the ε-selection)

[lean-pool-file-0001 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L171-L248) — **useful_candidate**.

The positive and negative active cases repeat a substantial scalar epsilon argument. A single lemma about absolute values and a signed perturbation has a clear mathematical statement and removes considerable repeated algebra. The exact helper has not been compiled.

### lean-pool: dual_cert_from_convexHull (h_sum_eq: positive and negative generator cases)

[lean-pool-file-0001 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L396-L435) — **useful_candidate**.

The source repeats the indicator-versus-negative-indicator disjointness argument in two generator branches and a disjointness proof. One precise lemma about their equality forcing empty sets is a credible shared fact.

### lean-pool: realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree

[lean-pool-file-0002 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364-L413) — **useful_candidate**.

The Leray and Stokes proofs repeat an equality-to-a.e.-equality transfer followed by the same orthogonality argument. A helper parameterised by the Fourier image plausibly removes a substantive repeated block.

### lean-pool: realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree

[lean-pool-file-0002 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384-L424) — **optional_refactor**.

The representative-conversion wrapper is repeated, but it is only a few lines and already uses the two appropriate named lemmas. A further one-line composite helper is optional, especially if the preceding larger refactor absorbs it.

### lean-pool: pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta vs pv_cutoff_integral_seg1_eq_inv / pv_cutoff_integral_seg2_eq_Ialpha / pv_cutoff_integral_seg3_eq_neg_inv

[lean-pool-file-0003 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L372-L398) — **useful_candidate**.

Three segment integrand formulas are each re-established for integrability and again for integral evaluation. Shared pointwise segment lemmas would remove genuine repeated calculations, not just common proof syntax.

### lean-pool: log_cancellation (duplicating integral_seg3_eq_log / integral_seg1_eq_neg_log)

[lean-pool-file-0003 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L291-L297) — **useful_candidate**.

The logarithmic cancellation proof redoes integral identities already proved earlier at a specialised endpoint. Generalising or directly reusing those lemmas is a concrete simplification with no speculative new abstraction.

### lean-pool: pv_cutoff_F_integrable_0_delta / pv_cutoff_F_integrable_3delta_3 / hI1 / hI5 in pv_sector_cutoff_eq

[lean-pool-file-0003 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L307-L340) — **useful_candidate**.

Pointwise cutoff vanishing is re-established both for integrability and for zero integral values. Stating the vanishing criterion once is a natural and reusable mathematical interface.

### lean-pool: norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le

[lean-pool-file-0004 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428) — **useful_candidate**.

First- and second-derivative decay proofs share the phase estimate and Gaussian absorption steps. Parameterising the nonnegative polynomial majorant gives a meaningful common argument, though not every line of the two proofs can be merged.

### lean-pool: fourier_poitouVerticalProfileDerivative_regularized / fourier_poitouVerticalProfileSecondDerivative_regularized

[lean-pool-file-0004 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L556-L580) — **optional_refactor**.

Both proofs specialise Real.fourier_deriv, which is itself the shared mathematical theorem. A HasDerivAt-facing helper may save scaffolding, but its type/proof and call-site costs need to be counted before calling this substantial duplication.

### lean-pool: poitouVerticalProfileDerivative_regularized_integrable / integrable_quadratic_abs_mul_exp_neg_mul_sq

[lean-pool-file-0004 finding 2](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L430-L449) — **useful_candidate**.

A later general polynomial-times-Gaussian integrability lemma covers the earlier first-derivative majorant with quadratic coefficient zero. Moving and reusing that existing result is a concrete net simplification.

### lean-pool: positiveShell_pairwise

[lean-pool-file-0005 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L160) — **useful_candidate**.

Four shell-disjointness proofs repeat the same ordered-radius contradiction with different index encodings. An integer-indexed disjointness lemma can cover all of them; the source comparisons confirm the repeated mathematical core.

### lean-pool: exists_positive_shell

[lean-pool-file-0005 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L128) — **useful_candidate**.

Positive and negative shell coverage repeat the log/floor construction and exponential bounds. Separating the general integer-shell existence statement from index-sign bookkeeping is a natural substantive abstraction.

### lean-pool: RS.dslope_const_mul / RS.dslope_const (with RS.dslope_sub_mul and Filter.EventuallyEq.dslope_eq)

[lean-pool-file-0006 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L82-L96) — **incorrect_or_incomplete_proposal**.

The cited proofs share a short diagonal/off-diagonal case split but have different right-hand-side operations. The proposed helper only compares dslope f with dslope g; it does not directly prove dslope(c*f)=c*dslope f as claimed. The abstraction is not demonstrated to cover the cited cases.

### lean-pool: RS.taylorCoeffAt_const_mul / RS.taylorCoeffAt_zero_fun / RS.taylorCoeffAt_congr / RS.taylorCoeffAt_sub_pow_mul

[lean-pool-file-0006 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L97-L103) — **incorrect_or_incomplete_proposal**.

The short inductions express different facts, including a germ relation and an index-shifting monomial identity. The proposed unary intertwining helper covers scalar multiplication but not all of those cases as stated. Shared induction syntax is insufficient evidence of a beneficial common lemma.

### lean-pool: weakPathRepresentative_pairing_eq_inner / FrozenDriftProblem.initial_pairing_eq_cell_integral

[lean-pool-file-0007 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188-L226) — **useful_candidate**.

The physical pairing and initial-data pairing repeat the torus representative, L2 inner-product and unit-cell integration argument. A lemma for an arbitrary torus L2 class and its physical representative has a clear common mathematical role.

### lean-pool: weakPathRepresentative_memL2On / weakPathRepresentative_l2NormSq / weakPathRepresentative_pairing_eq_inner

[lean-pool-file-0007 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184) — **optional_refactor**.

A weakPathRepresentative_of_mem simp lemma is useful API, but the repeated evaluation proof is only a few lines. This fits a small simp-interface improvement better than substantial repeated proof machinery.

### lean-pool: planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C / planeCurveToBivariate_natDegree_eq_degreeOf_zero

[lean-pool-file-0008 finding 0](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L54-L110) — **optional_refactor**.

An apply lemma would hide a repeated explicit composition shape, and standard generator computation lemmas could simplify the proofs. Much of the proposed gain is API use/proof shortening rather than extraction of a substantial shared mathematical argument.

### lean-pool: planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials / ..._of_absoluteIrreducible / ..._of_absoluteIrreducible_coordinateDegrees (and the main theorem)

[lean-pool-file-0008 finding 1](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L436-L554) — **useful_candidate**.

Several theorem variants repeat nontrivial function-field instance and irreducibility setup, including copies in both statements and proofs. Shared setup and the existing absolute-irreducibility lemma are concrete candidates, with import/coherence checks still required.

### mathlib: DFinsupp.support_rangeIcc_subset (also repeated in DFinsupp.rangeIcc)

[mathlib-file-0001 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L115-L123) — **not_established**.

The suggested Icc_zero_zero helper is already Icc_self. The support proofs use different representations and their remaining membership reasoning is not removed by renaming that one-line identity. This does not establish missing substantial shared machinery.

### mathlib: Profinite.effectiveEpiFamily_tfae

[mathlib-file-0002 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L74-L91) — **optional_refactor**.

The Profinite/Stonean transfer proofs have a genuine common pattern. However, the proposed generic helper leaves key concrete-category/underlying-function assumptions informal and may cost more infrastructure than it saves. This needs a precise valid statement before treating it as a defect.

### mathlib: Profinite.effectiveEpi_tfae and the PreservesEffectiveEpis / ReflectsEffectiveEpis instances for profiniteToCompHaus

[mathlib-file-0002 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L35-L53) — **not_established**.

The TFAE proof and preservation/reflection instances are already very short applications of existing equivalences. A new generic concrete-category interface is not shown to improve the net code or readability.

### mathlib: Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow

[mathlib-file-0003 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293) — **optional_refactor**.

The real/natural proofs do share a roughly six-line estimate. A general-filter helper is possible, but its statement and extra parameters have a cost. This is an optional abstraction, not a clear substantial duplication defect.

### mathlib: Complex.isBigO_cpow_rpow / Complex.isTheta_cpow_rpow

[mathlib-file-0003 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L185-L206) — **optional_refactor**.

The repeated tail consists of applying the same bounded-exponential equivalence and simplifying division by one. A long new auxiliary statement is not clearly a net improvement over those short calc steps.

### mathlib: Bundle.Trivialization.mk_coordChangeL and Bundle.VectorPrebundle.mk_coordChange

[mathlib-file-0006 finding 0](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L323) — **optional_refactor**.

The existing mk_proj_snd lemma appears to shorten both coordinate-change proofs directly. That is a concrete API-use simplification; no new shared helper is needed, and the repeated proof itself is modest.

### mathlib: Bundle.Trivialization.coordChangeL (continuous_toFun / continuous_invFun)

[mathlib-file-0006 finding 1](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L275-L292) — **useful_candidate**.

The forward and inverse continuity arguments are sizeable mirror images. A local one-directional continuity lemma used twice would expose the symmetry and remove repeated composition reasoning without requiring a large public API.

### mathlib: Bundle.Trivialization.continuousLinearMapAt and continuousLinearEquivAt (and symmL)

[mathlib-file-0006 finding 2](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L398-L456) — **optional_refactor**.

The exact forward-continuity term is repeated, so a fibrewise continuity lemma is plausible API. The inverse direction already uses symmL.continuous rather than rebuilding the same proof. The claimed three-way duplication is overstated and the net saving is modest.

### tauceti: TauCeti.ReducedTensorWords.isCoderivation_coderiv

[tauceti-file-0001 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L346-L399) — **useful_candidate**.

The ungraded and graded co-Leibniz proofs visibly repeat a long deconcatenation and triangle-reindexing argument. A shared combinatorial core is worth extracting. The proposed arbitrary-tuple formulation needs compatibility assumptions; I do not endorse its exact statement or claimed line count without a checked refactor.

### tauceti: TauCeti.ReducedTensorWords.letter_comp_coderiv

[tauceti-file-0001 finding 1](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L438-L451) — **useful_candidate**.

Both Taylor-component proofs isolate the sole whole-word splice using the same nested sum_eq_single argument. A whole-word evaluation lemma is a precise natural helper, with the graded twist handled at its particular call site.

### tauceti: Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup

[tauceti-file-0003 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L76-L82) — **optional_refactor**.

The scalar-matrix assembly is genuinely shared, but short. A general characterisation may be useful independently; its empty-index case and algebraic assumptions need to be stated correctly. The saving alone is not compelling.

### tauceti: continuousOn_schwarzChristoffelBoundary / schwarzChristoffelBoundary_sub_eq / schwarzChristoffelBoundary_injOn / collinear_schwarzChristoffelBoundary_image

[tauceti-file-0004 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L165-L248) — **useful_candidate**.

Several boundary theorems transfer properties from the same unique continuous extension witness. Packaging the canonical boundary identification and its consequences once has a coherent mathematical role, particularly for the image-set proof.

### tauceti: TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg

[tauceti-file-0005 finding 0](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L104-L133) — **useful_candidate**.

The Killing-pairing cancellation and cyclic/skew-symmetry manipulation recur in the Chevalley and non-Chevalley variants. A shared symmetry identity is credible. Merely wrapping the already short nonvanishing application or a ring calculation would not by itself justify the finding.
