# definition-fidelity: run `defs1`, judge `claude-opus-5-5-high`

| Library | Sampled | Judged | `not_a_mathematical_object` | `unclear` | Assessed | Flagged | `incorrect` | `too_narrow` | `no_docstring` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 100 | 100 | 17 | 0 | 83 | 1 | 0 | 1 | 0 | 1.2% | 0.2%–6.5% | $4.28 |
| Tau Ceti | 100 | 100 | 12 | 0 | 88 | 3 | 0 | 3 | 0 | 3.4% | 1.2%–9.5% | $12.31 |
| Lean Pool | 100 | 100 | 58 | 0 | 42 | 2 | 0 | 2 | 0 | 4.8% | 1.3%–15.8% | $6.83 |
| FLT (Anthropic) | 100 | 100 | 0 | 0 | 100 | 100 | 0 | 0 | 100 | 100.0% | 96.3%–100.0% | $0.00 |
| Formal Frontier | 100 | 100 | 27 | 0 | 73 | 3 | 0 | 3 | 0 | 4.1% | 1.4%–11.4% | $11.25 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (1 flagged)

### [`nullSubgroup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Group/NullSubmodule.lean#L36-L46) — `mathlib-0023`

Snippet: `samples/mathlib/mathlib-0023.lean`

- **verdict**: `too_narrow`
- **intended_object**: The null subgroup of a seminormed group M: the subgroup {x ∈ M | ‖x‖ = 0} (the kernel of the seminorm). Inferred from the docstring, the module docs and the name.
- **explanation**: The definition is correct: the carrier is {x | ‖x‖ = 0}. Closure under the group operations follows from norm_one', the triangle inequality norm_mul_le' and norm_inv'. However, the definition assumes [SeminormedCommGroup M], while all three lemmas it uses are stated in Mathlib for an arbitrary [SeminormedGroup E] (section SeminormedGroup in Mathlib/Analysis/Normed/Group/Basic.lean). Commutativity is never used, and the same body compiles verbatim for SeminormedGroup. The null subgroup of a group seminorm is a standard notion for non-abelian groups as well. In a seminormed group it equals the closure of {1}, since ‖x‖ = dist(x, 1), and that closure is even a normal subgroup. So the multiplicative definition should be stated for SeminormedGroup. The additive version derived from it can still be specialized for the submodule part, which genuinely needs commutativity. No other Mathlib declaration defines this subgroup.


## Tau Ceti (3 flagged)

### [`spatialFDeriv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Calculus/ParametricFDeriv.lean#L86-L89) — `tauceti-0014`

Snippet: `samples/tauceti/tauceti-0014.lean`

- **verdict**: `too_narrow`
- **intended_object**: The spatial Jacobian of a parametric map F(t, x): for fixed x, the function t ↦ D₂F(t, x), i.e. the partial Fréchet derivative of F in the spatial variable x. It is taken here as the total derivative of F at (t, x) restricted to the E factor, with the documented junk value 0 where F is not jointly differentiable. Inferred from the docstring, the module documentation and the lemmas `hasFDerivAt_timeSlice` and `fderiv_timeSlice`.
- **explanation**: The body is `(fderiv 𝕜 F (t, x)).comp (inr 𝕜 𝕜 E)`, the total derivative restricted to the second factor. Wherever F is differentiable at (t, x) this equals the partial derivative D₂F(t, x), as `fderiv_timeSlice` shows. The value 0 at points where F is not jointly differentiable is stated in the docstring, so I treat it as a deliberate junk-value choice rather than an error, even though the textbook partial derivative also exists at points where only the slice y ↦ F(t, y) is differentiable.

It is too narrow because the parameter space is fixed to the scalar field 𝕜. The construction uses no property of 𝕜 as a parameter space. `fderiv 𝕜 F (p, x) ∘L inr 𝕜 P E` makes sense for F : P × E → F' with P any normed 𝕜-space, and the partial derivative D₂F on a product of normed spaces is the standard notion in the literature. Only the companion definition `timeFDeriv` needs a scalar parameter, because it evaluates at the direction (1, 0); `spatialFDeriv` does not. The library itself shows the restriction matters:
- The module docstring describes maps `F : P × E → F'` with a general parameter space P.
- The main mixed-derivative theorem, `TauCeti.hasFDerivAt_spatialFDeriv`, is stated for a general normed parameter space P. It cannot use `spatialFDeriv` and writes `fun q ↦ fderiv 𝕜 (fun y ↦ F (q, y)) x` by hand instead.

Mathlib has no partial-Fréchet-derivative definition (I found no `partialFDeriv` or similar), so there is no counterpart to cite. Still, the natural generality is a general normed parameter space P, not 𝕜.

### [`LinearMap.BilinForm.dualSubmoduleEquivDual`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/BilinearForm/DualLattice.lean#L79-L87) — `tauceti-0022`

Snippet: `samples/tauceti/tauceti-0022.lean`

- **verdict**: `too_narrow`
- **intended_object**: The perfect-duality isomorphism N^∨ ≅ Hom_R(N, R), where N is a full R-lattice in a finite-dimensional K-vector space V (K = Frac R), B is a nondegenerate bilinear form on V, and N^∨ = {x ∈ V : B(x, N) ⊆ R} is the dual lattice. The map sends x to y ↦ B(x, y). This comes from the docstring and from the TODO on Mathlib's `dualSubmoduleToDual`, which says "Show that this is perfect when `N` is a lattice and `B` is nondegenerate".
- **explanation**: The construction itself is correct. It bundles Mathlib's canonical pairing `B.dualSubmoduleToDual N` with `LinearEquiv.ofBijective`. Injectivity is Mathlib's `dualSubmoduleToDual_injective`, which needs only nondegeneracy and that N spans V. Surjectivity is the library's lemma, which uses an R-basis of N, so the map is the intended one.

The problem is the extra hypothesis `[Module.Free R N]`. The statement holds for every full lattice in Mathlib's sense, `Submodule.IsLattice K` (a finitely generated R-submodule whose K-span is V), with no freeness. Proof sketch: take f : N → R. Because K is the fraction field and N spans V, every v ∈ V has some nonzero d ∈ R with d·v ∈ N. Then f_K(v) := f(d·v)/d is a well-defined K-linear extension of f to V → K. V is finite-dimensional because N is finitely generated and spans V, so nondegeneracy of B gives some x with B(x, ·) = f_K. This x lies in the dual submodule and maps to f. No basis of N is needed.

In the standard setting of lattices over a Dedekind domain (Reiner, Neukirch; fractional ideals, the inverse different), lattices are projective but in general not free. So the freeness assumption excludes cases where the notion is standard and the isomorphism holds. Mathlib's own TODO states the goal for any lattice N, not a free one. Freeness is a proof convenience here (it allows `extendOfIsLattice` and `dualBasis`), not something the object requires. So the definition is correct but stated in narrower generality than its natural one.

### [`TauCeti.D4Tripled.d4BlockTwoToZeroEquiv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/D4/Tripled/BlockIntertwiners.lean#L286-L289) — `tauceti-0044`

Snippet: `samples/tauceti/tauceti-0044.lean`

- **verdict**: `too_narrow`
- **intended_object**: The triality intertwiner from block 2 to block 0 of the tripled D₄ weight table: the linear isomorphism, in coordinates, from the half-spin representation V(ϖ₄) to the vector representation V(ϖ₁). It reindexes coordinates along the order-three triality permutation (inferred from the docstring and the module documentation).
- **mathlib_counterpart**: LinearEquiv.piCongrLeft'
- **explanation**: The body is `LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockTwoToZeroIndexEquiv`, a pure reindexing of coordinate vectors along the bijection `Block 2 ≃ Block 0`. That bijection is the library's `blockIndexEquiv 2` followed by a cast that rewrites `Block (finRotate 3 2)` as `Block 0`. The construction is correct: the library proves the cycle identity and the intertwining of the raising, lowering and Cartan generator matrices. However, nothing in it uses anything about ℚ. `piCongrLeft'` works over any semiring, and the generator matrices are integer matrices that can be cast into any ring. The same file already defines the construction over an arbitrary semiring as `blockModuleEquiv R j`, and its module documentation says each restricted equivalence "induces a linear equivalence over every semiring". This definition copies that construction with the ring fixed to ℚ, adding only the rewrite of the index type `Block (finRotate 3 2)` to `Block 0`, which needs no special property of ℚ. The natural setting is an arbitrary (semi)ring R, with type `(Block 2 → R) ≃ₗ[R] (Block 0 → R)`. Fixing ℚ is an unneeded narrowing of a construction the library itself states in general.


## Lean Pool (2 flagged)

### [`CKN.Foundation.Euclidean.lpPairingWith`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/LpExtension.lean#L468-L474) — `lean-pool-0041`

Snippet: `samples/lean-pool/lean-pool-0041.lean`

- **verdict**: `too_narrow`
- **intended_object**: For a fixed g ∈ L^q, the continuous linear functional f ↦ ∫ f g on L^p, with p and q Hölder conjugates. This is the canonical map from L^q into the dual of L^p. Inferred from the docstring and from the lemma `lpPairingWith_apply` (`= ∫ x, f x * g x`).
- **mathlib_counterpart**: ContinuousLinearMap.lpPairing
- **explanation**: The definition is correct. It takes Mathlib's `ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ)`, which by `lpPairing_eq_integral` is f ↦ g ↦ ∫ f(x) g(x) dx, and evaluates it at the fixed g using `ContinuousLinearMap.apply`. The result is the functional f ↦ ∫ f g, as the docstring says.

The problem is the setting. The definition is fixed to `Vec3` (ℝ³) with Lebesgue measure `volume`, but nothing in the body uses that setting. Mathlib's `lpPairing` works for any measure space (α, μ), with any Hölder-conjugate exponents and any continuous bilinear map B : E →L F →L G.

The Hölder pairing against a fixed function in the conjugate space is standard on an arbitrary measure space. Here it is just Mathlib's general construction written out for ℝ³ with Lebesgue measure. A general version would take a measure μ on any measurable space, and perhaps a general scalar field 𝕜 or a bilinear map B. So the definition is too narrow, and its general counterpart is `ContinuousLinearMap.lpPairing`.

### [`quadForm`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OSforGFF/Bochner/Sazonov.lean#L62-L63) — `lean-pool-0094`

Snippet: `samples/lean-pool/lean-pool-0094.lean`

- **verdict**: `too_narrow`
- **intended_object**: The quadratic form x ↦ ⟪x, Sx⟫ of a bounded operator S on a real inner product space (from the docstring). In the module it is used for positive operators in the proof of Sazonov's theorem.
- **mathlib_counterpart**: ContinuousLinearMap.reApplyInnerSelf
- **explanation**: The body, `inner x (S x)`, does compute ⟪x, Sx⟫ correctly. But because of the section `variable` line, the definition also carries `[CompleteSpace H]` as an instance argument. Lean 4 automatically includes an instance-implicit variable once all the types it mentions are included, and this one mentions only `H`. The construction never uses completeness: it only needs a real inner product space, and the continuity of S comes from the type `H →L[ℝ] H`.

Mathlib already provides this construction in general. `ContinuousLinearMap.reApplyInnerSelf` (in Mathlib/Analysis/InnerProductSpace/LinearMap.lean) is defined as `re ⟪T x, x⟫` for any continuous linear endomorphism of an inner product space over an `RCLike` field 𝕜, with no completeness assumption. Over ℝ, `re` is the identity and the inner product is symmetric, so `reApplyInnerSelf S x = ⟪S x, x⟫ = ⟪x, S x⟫ = quadForm S x`. Mathlib also states `IsPositive` in terms of `reApplyInnerSelf`.

So `quadForm` is a re-implementation of a Mathlib construction, restricted to ℝ and to complete spaces. The definition's own content needs neither restriction; completeness only matters for later results in the file about Sazonov's theorem.


## FLT (Anthropic) (100 flagged)

### [`P2MW.S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two.STAB2E100.negVC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_torsionOrbit_bot_eq_two.lean#L65-L65) — `flt-anthropic-0000`

Snippet: `samples/flt-anthropic/flt-anthropic-0000.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor.entryAdele`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.lean#L241-L245) — `flt-anthropic-0001`

Snippet: `samples/flt-anthropic/flt-anthropic-0001.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.SubalgebraStages.specCone`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_SubalgebraStages.lean#L50-L55) — `flt-anthropic-0002`

Snippet: `samples/flt-anthropic/flt-anthropic-0002.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.OrbitStabFin.underS`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above.lean#L34-L34) — `flt-anthropic-0003`

Snippet: `samples/flt-anthropic/flt-anthropic-0003.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.P2mInertEvalGlue.unitNorm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_eq_ite_finrank_mul_sum_of_isTwistedWeightedOrbitalIntegral_indicator_semiLocalIntegralSet_of_relIndex_eq_of_subsingleton_extension.lean#L240-L241) — `flt-anthropic-0004`

Snippet: `samples/flt-anthropic/flt-anthropic-0004.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules.FrameBridge.secX`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean#L65-L65) — `flt-anthropic-0005`

Snippet: `samples/flt-anthropic/flt-anthropic-0005.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two.W1xLA.τEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_two.lean#L976-L977) — `flt-anthropic-0006`

Snippet: `samples/flt-anthropic/flt-anthropic-0006.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.J1ThirteenPlaneModel.J1ThirteenPicZeroFibreDiamond.J1ThirteenPicZeroLiteralChordChain.J1ThirteenPicZeroPlaceDictionary.J1ThirteenPicZeroPlaceDictionary.PlaceConstruction.J1ThirteenPicZeroLitPic0Comparison.J1ThirteenX113RiemannRochRows.MazurTate1973Mt31b.J1ThirteenX113PackageHeldRowOne.MilneAvAg9bRd9DictionaryHeld3Closure.J1ThirteenX113OrdRowWellDefinedReduction.MilneAvAg9bRd10EllKFinUpperRow.MilneAvAg9bRd11X113TowerPowerBasis.Ag9b11bX113HwdUnitDischarge.MilneAvAg9bRd11DictionaryBinderShrink.MilneAvAg9bRd12X113AssemblyRetirement.MilneAvAg9bRd12T1P1InftyResidue.MilneAvAg9bRd12X113LocalDatumMint.MilneAvAg9bRd12X113FiveRowUpgrade.AlgebraicCurve.HasSeparatingTranscendentalCore`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L9415-L9416) — `flt-anthropic-0007`

Snippet: `samples/flt-anthropic/flt-anthropic-0007.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CuspForm.AuxLevel.midML`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CuspForm_AuxLevelHeckeModuleMid.lean#L31-L34) — `flt-anthropic-0008`

Snippet: `samples/flt-anthropic/flt-anthropic-0008.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.AlgebraicGeometry.RelPicard.K3Far.liftSnd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_and_finrank_H0_restrict_snd_of_farBlocks_of_twoGluedSmoothCurveDegeneration.lean#L93-L102) — `flt-anthropic-0009`

Snippet: `samples/flt-anthropic/flt-anthropic-0009.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.RATIOCOVER.weyl`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.lean#L29-L37) — `flt-anthropic-0010`

Snippet: `samples/flt-anthropic/flt-anthropic-0010.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicGeometry.Scheme.Modules.IsSectionBasisOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_FramedPolarisedAbelianScheme.lean#L17-L20) — `flt-anthropic-0011`

Snippet: `samples/flt-anthropic/flt-anthropic-0011.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.SIdeleRealisation.pre`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply.lean#L455-L462) — `flt-anthropic-0012`

Snippet: `samples/flt-anthropic/flt-anthropic-0012.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.Ws31.SW3.IsKfSm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_norm_sub_le_of_continuous_invariant_bandSupported.lean#L61-L63) — `flt-anthropic-0013`

Snippet: `samples/flt-anthropic/flt-anthropic-0013.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.AlgebraicGeometry.RelPicard.LFP.fromOrient`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.lean#L354-L359) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.PDPairing.sect`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_PDPairing.lean#L461-L462) — `flt-anthropic-0015`

Snippet: `samples/flt-anthropic/flt-anthropic-0015.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two.MuTwoGroupAlgebraRepr.GroupAlgebraPoints.C2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_sectionsEquiv_algHom_muP_of_bialgEquiv_monoidAlgebra_two.lean#L163-L163) — `flt-anthropic-0016`

Snippet: `samples/flt-anthropic/flt-anthropic-0016.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel.zeta0`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.lean#L868-L869) — `flt-anthropic-0017`

Snippet: `samples/flt-anthropic/flt-anthropic-0017.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.BridgeCup.zetaq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.lean#L408-L411) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.lean#L2189-L2194) — `flt-anthropic-0019`

Snippet: `samples/flt-anthropic/flt-anthropic-0019.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD.divP`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.lean#L158-L158) — `flt-anthropic-0020`

Snippet: `samples/flt-anthropic/flt-anthropic-0020.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.FormalOmega.AlgFunctor.GroupAction`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean#L60-L67) — `flt-anthropic-0021`

Snippet: `samples/flt-anthropic/flt-anthropic-0021.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.P2mOctCompare.Hex`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_ExplicitLift_trace_det_eq_of_agreeUpToPartner_of_conjPow.lean#L13-L13) — `flt-anthropic-0022`

Snippet: `samples/flt-anthropic/flt-anthropic-0022.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`NeronModelInfra.schemeHomOverEquivOverHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean#L46-L51) — `flt-anthropic-0023`

Snippet: `samples/flt-anthropic/flt-anthropic-0023.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4.W1xLA.Good`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_four_qExpansion_eq_c4.lean#L841-L842) — `flt-anthropic-0024`

Snippet: `samples/flt-anthropic/flt-anthropic-0024.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.B28U3.S`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.lean#L230-L232) — `flt-anthropic-0025`

Snippet: `samples/flt-anthropic/flt-anthropic-0025.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.ModularCurve.PDPairing.TD.HFun`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean#L2707-L2709) — `flt-anthropic-0026`

Snippet: `samples/flt-anthropic/flt-anthropic-0026.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot.TateTransfer.Arith.sB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_variableChange_veluQuotient2_tateLaurent_eq_and_vcXInv_velu2X_toricPoint_eq_of_isPrimitiveRoot.lean#L87-L87) — `flt-anthropic-0027`

Snippet: `samples/flt-anthropic/flt-anthropic-0027.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH.ModularCurve.LinAuxW.expZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero_of_diffQExp_apply_eq_intSeriesC_alSlash_diamondLinH.lean#L232-L232) — `flt-anthropic-0028`

Snippet: `samples/flt-anthropic/flt-anthropic-0028.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.Ws25.KummerO.PointsDict.pointsEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial.lean#L1721-L1725) — `flt-anthropic-0029`

Snippet: `samples/flt-anthropic/flt-anthropic-0029.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.XI`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean#L17-L17) — `flt-anthropic-0030`

Snippet: `samples/flt-anthropic/flt-anthropic-0030.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex.AVC15.pairPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_tendsto_appLE_complex.lean#L57-L58) — `flt-anthropic-0031`

Snippet: `samples/flt-anthropic/flt-anthropic-0031.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.FinFlatHopf.FinFlatHopf.W4.moduleScal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic.lean#L1441-L1443) — `flt-anthropic-0032`

Snippet: `samples/flt-anthropic/flt-anthropic-0032.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.TPIN.Ent`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq.lean#L234-L236) — `flt-anthropic-0033`

Snippet: `samples/flt-anthropic/flt-anthropic-0033.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.CerednikDrinfeld.KernelIdealDescent.homGrp`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_dualPair_image_kernelIdealSet_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_finiteAdeleBox.lean#L258-L262) — `flt-anthropic-0034`

Snippet: `samples/flt-anthropic/flt-anthropic-0034.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.CyclicLevelAverageEngine.Setup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_InnerProductSpace_exists_mem_norm_sub_lt_of_exists_mem_span_orbit_of_average.lean#L15-L42) — `flt-anthropic-0035`

Snippet: `samples/flt-anthropic/flt-anthropic-0035.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime.CerednikDrinfeld.QM.FakeEllipticCurve.Pts.val`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_generator_torsionPoints_of_isMaximalOrder_of_prime.lean#L59-L59) — `flt-anthropic-0036`

Snippet: `samples/flt-anthropic/flt-anthropic-0036.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isEichlerOrder_forall_mem_awayUnits_iff_forall_exists_smul_mem_preservesLevel_and_exists_isMaximalOrder_inf_eq_of_isPullback_prod.LStabAsm.e10`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isEichlerOrder_forall_mem_awayUnits_iff_forall_exists_smul_mem_preservesLevel_and_exists_isMaximalOrder_inf_eq_of_isPullback_prod.lean#L475-L478) — `flt-anthropic-0037`

Snippet: `samples/flt-anthropic/flt-anthropic-0037.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.NumberField.AdelicFourier.RowModule.rowModulus`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul.lean#L247-L250) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.CerednikDrinfeld.QM.EnumAux.basePt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_quotients_of_card_eq_mul_sq.lean#L163-L164) — `flt-anthropic-0039`

Snippet: `samples/flt-anthropic/flt-anthropic-0039.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_M4aHerbrand_adeleBaseChange_local_rigidity.M4aHerbrand.Rigidity.singleFinStratum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_M4aHerbrand_adeleBaseChange_local_rigidity.lean#L414-L421) — `flt-anthropic-0040`

Snippet: `samples/flt-anthropic/flt-anthropic-0040.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam.LambdaGhost.inv1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_BigWittLaw_subst_artinHasse_frobFam.lean#L30-L30) — `flt-anthropic-0041`

Snippet: `samples/flt-anthropic/flt-anthropic-0041.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LanglandsTunnell_CubicInduction_seed_package_of_mem_span_archDeriv_translate.R1CuspDeriv.ofRealHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_seed_package_of_mem_span_archDeriv_translate.lean#L80-L81) — `flt-anthropic-0042`

Snippet: `samples/flt-anthropic/flt-anthropic-0042.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`CerednikDrinfeld.Omega.edgeTube`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_CerednikDrinfeld_OmegaTubes.lean#L29-L30) — `flt-anthropic-0043`

Snippet: `samples/flt-anthropic/flt-anthropic-0043.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.R1Kit.twistStepTopIso`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.lean#L133-L137) — `flt-anthropic-0044`

Snippet: `samples/flt-anthropic/flt-anthropic-0044.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.R4EmbedM2.retr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_exists_algHom_matrix_injective_of_isDefiniteRamifiedExactlyAt_of_forall_isUnit.lean#L20-L21) — `flt-anthropic-0045`

Snippet: `samples/flt-anthropic/flt-anthropic-0045.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`MvPolynomial.CrossingQuotient.quotIUEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_MvPolynomial_CrossingResolutionFibrePoints.lean#L676-L678) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint.W1xLA.qC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_modularForm_weight_three_qExpansion_eq_cuspPoint.lean#L361-L361) — `flt-anthropic-0047`

Snippet: `samples/flt-anthropic/flt-anthropic-0047.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`ModularCurve.MultCovering.nodeSrc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_MultCoveringCharts.lean#L123-L124) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.ESD3.idxEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_finrank_cornerSubmodule_H1_eq_two_mul_of_not_isEisenstein.lean#L425-L426) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`MvFormalGroup.ofMv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_MvFormalGroup_OfFormalGroupV2.lean#L198-L198) — `flt-anthropic-0050`

Snippet: `samples/flt-anthropic/flt-anthropic-0050.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.B26.rO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle.lean#L19-L20) — `flt-anthropic-0051`

Snippet: `samples/flt-anthropic/flt-anthropic-0051.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.S17Torsor.β`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span.lean#L131-L132) — `flt-anthropic-0052`

Snippet: `samples/flt-anthropic/flt-anthropic-0052.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom.principalIdeles`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.lean#L25-L26) — `flt-anthropic-0053`

Snippet: `samples/flt-anthropic/flt-anthropic-0053.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.S42LevelHopf.Calg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_exists_hopfAlgebra_presentation_comul_eq_of_cocycle_of_powerDefect.lean#L109-L109) — `flt-anthropic-0054`

Snippet: `samples/flt-anthropic/flt-anthropic-0054.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.Theta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1241-L1245) — `flt-anthropic-0055`

Snippet: `samples/flt-anthropic/flt-anthropic-0055.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.P2mKcQmBcSol.SqHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback.lean#L75-L77) — `flt-anthropic-0056`

Snippet: `samples/flt-anthropic/flt-anthropic-0056.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand.R4GC.upSL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_isLevelAutAt_apply_eq_iff_exists_eq_qExpand.lean#L102-L102) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.Sum56K6.i6`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_KatzModularForm_toFun_eq_zero_of_weight_two_of_isUnit_six.lean#L481-L481) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.Differential.pullbackAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_DifferentialPushPull.lean#L16-L19) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`WeierstrassCurve.variableChangeDenom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_VariableChangeSeries.lean#L14-L15) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_PadicInt_exists_etale_algebra_algHom_equiv_zmod.UnramLayer.kOf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PadicInt_exists_etale_algebra_algHom_equiv_zmod.lean#L254-L255) — `flt-anthropic-0061`

Snippet: `samples/flt-anthropic/flt-anthropic-0061.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.WeierstrassCurve.Affine.mapPoint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean#L6641-L6642) — `flt-anthropic-0062`

Snippet: `samples/flt-anthropic/flt-anthropic-0062.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio.FLT.AdmissibleRep.fixedVectors`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio.lean#L1391-L1400) — `flt-anthropic-0063`

Snippet: `samples/flt-anthropic/flt-anthropic-0063.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one.M4aLocalCFT.FujisakiC2a.unitElem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one.lean#L3699-L3699) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.IsModuliPlaceOfFrobSmulSol.twPlace`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isModuliPlaceOf_map_frobenius_smul.lean#L37-L43) — `flt-anthropic-0065`

Snippet: `samples/flt-anthropic/flt-anthropic-0065.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.IsIntegralAdjoinCoeffEmbJqInvSol.Lc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_pow_of_cuspForm_mul_thetaL_pow_eq_qExpansion.lean#L116-L117) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal.tMi`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.lean#L430-L430) — `flt-anthropic-0067`

Snippet: `samples/flt-anthropic/flt-anthropic-0067.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`AlgebraicCurve.comapSubschemeMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_UniversalDivisor.lean#L74-L76) — `flt-anthropic-0068`

Snippet: `samples/flt-anthropic/flt-anthropic-0068.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.KbManinAnyChar.sig3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.lean#L552-L552) — `flt-anthropic-0069`

Snippet: `samples/flt-anthropic/flt-anthropic-0069.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.Ws50Read.shuffle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_addEquiv_proj_snd_eq_pic0Mk_single_sub_single_of_points_eq_reduction_of_poincare_iso_ofPoint_valuationSubring_twoChartModel_x1_mul.lean#L77-L79) — `flt-anthropic-0070`

Snippet: `samples/flt-anthropic/flt-anthropic-0070.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.E4AV_CuPoleFst.algebraFbShortcut`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_pole_reduceFst_of_regularityLaw_of_coe_of_unit_of_cusp_of_orient.lean#L61-L62) — `flt-anthropic-0071`

Snippet: `samples/flt-anthropic/flt-anthropic-0071.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.WhitIBP.ℓ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean#L310-L310) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.EsUPar.PerU.beta`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_exists_isEigenformWith_qCoeff_eq_of_mem_parabolicHoms_of_heckeT_eq_smul.lean#L165-L166) — `flt-anthropic-0073`

Snippet: `samples/flt-anthropic/flt-anthropic-0073.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.G4Sol.OA`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_iterCech_cols_exact_of_isQuasicoherent.lean#L426-L426) — `flt-anthropic-0074`

Snippet: `samples/flt-anthropic/flt-anthropic-0074.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots.GaussPencil.ratFuncMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots.lean#L394-L399) — `flt-anthropic-0075`

Snippet: `samples/flt-anthropic/flt-anthropic-0075.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`TwoChartCech.Mumford.quot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_MumfordTruncation.lean#L56-L57) — `flt-anthropic-0076`

Snippet: `samples/flt-anthropic/flt-anthropic-0076.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.AlgStructAux.ASys.T3`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_coequifibered_addEquiv_of_affHom_pushforwardUnit_of_isAdicComplete_of_isProper.lean#L269-L269) — `flt-anthropic-0077`

Snippet: `samples/flt-anthropic/flt-anthropic-0077.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`GaloisRep.InertiaRing.mkO`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GaloisRep_InertiaRing.lean#L32-L35) — `flt-anthropic-0078`

Snippet: `samples/flt-anthropic/flt-anthropic-0078.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.WeierstrassCurve.Affine.pointPullbackHomTo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_functionField_baseChange_finrankAlong_eq.lean#L456-L460) — `flt-anthropic-0079`

Snippet: `samples/flt-anthropic/flt-anthropic-0079.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness.QB.sPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_descent_raynaudQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness.lean#L190-L190) — `flt-anthropic-0080`

Snippet: `samples/flt-anthropic/flt-anthropic-0080.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.TwistMain.coordW`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep.lean#L595-L595) — `flt-anthropic-0081`

Snippet: `samples/flt-anthropic/flt-anthropic-0081.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.AlgebraicCurve.CentredPlaceRigidity.evalMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean#L173-L174) — `flt-anthropic-0082`

Snippet: `samples/flt-anthropic/flt-anthropic-0082.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.PInf`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L272-L273) — `flt-anthropic-0083`

Snippet: `samples/flt-anthropic/flt-anthropic-0083.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel.L1Asm22.Main.Zsub`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_finite_etale_represents_extraLevel.lean#L1790-L1790) — `flt-anthropic-0084`

Snippet: `samples/flt-anthropic/flt-anthropic-0084.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.EDB.Coord.N1'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient.lean#L224-L225) — `flt-anthropic-0085`

Snippet: `samples/flt-anthropic/flt-anthropic-0085.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.OmegaPull.kdAb`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq.lean#L474-L482) — `flt-anthropic-0086`

Snippet: `samples/flt-anthropic/flt-anthropic-0086.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.LC2.mass`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean#L379-L379) — `flt-anthropic-0087`

Snippet: `samples/flt-anthropic/flt-anthropic-0087.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.ModularCurve.PDPairing.TD.faceGen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_pairZFun_jDeg0_iDeg0.lean#L4974-L4974) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.ModularCurve.FullLevel.K1Road.qExpandBar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_relfinrank_adjoin_qExpand_image_laurentBaseChange_gamma0_fieldBar_ne_zero.lean#L41-L49) — `flt-anthropic-0089`

Snippet: `samples/flt-anthropic/flt-anthropic-0089.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.GoodReductionJacobian.RelativeGroupLaw.SpreadEtale.fstPt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_etale_preimage_snd_action_of_etale_nhds.lean#L38-L39) — `flt-anthropic-0090`

Snippet: `samples/flt-anthropic/flt-anthropic-0090.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.NilYoneda.transition`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_of_natural_of_isNilpotent.lean#L227-L228) — `flt-anthropic-0091`

Snippet: `samples/flt-anthropic/flt-anthropic-0091.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq.FltWs24.Asm.D2`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq.lean#L851-L859) — `flt-anthropic-0092`

Snippet: `samples/flt-anthropic/flt-anthropic-0092.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData.prπ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean#L140-L140) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_PDPairing_isFreeGroup_Gamma_four.ModularCurve.PDPairing.BaseTwo.cuspGen`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_isFreeGroup_Gamma_four.lean#L2065-L2067) — `flt-anthropic-0094`

Snippet: `samples/flt-anthropic/flt-anthropic-0094.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.TWExt.Θ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_HeckeData_exists_linearEquiv_ML_of_toML_op_sub_opAlgHom_pow_mem.lean#L38-L40) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.C2.EV`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_linearMap_H1_top_periodLattice_hom_heckeTL_eq_comp_of_mem_parabolicHoms.lean#L117-L118) — `flt-anthropic-0096`

Snippet: `samples/flt-anthropic/flt-anthropic-0096.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_TateCurve_symAdd_sum_regional.TateCurve.TateCurve.TateCurve.s1PosSupport`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_symAdd_sum_regional.lean#L2876-L2876) — `flt-anthropic-0097`

Snippet: `samples/flt-anthropic/flt-anthropic-0097.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.NormKit.S`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_normModule_frameKit_of_isClosedImmersion.lean#L744-L748) — `flt-anthropic-0098`

Snippet: `samples/flt-anthropic/flt-anthropic-0098.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.

### [`P2MW.S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.TOLD0b.Γ1`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean#L24-L25) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- **verdict**: `no_docstring`
- **explanation**: No docstring: what the declaration is meant to be is undocumented. Flagged by rule, without a judge.


## Formal Frontier (3 flagged)

### [`TopCat.Sheaf.OpenBaseChange.baseChangeIso`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenBaseChange.lean#L163-L204) — `formal-frontier-0031`

Snippet: `samples/formal-frontier/formal-frontier-0031.lean`

- **verdict**: `too_narrow`
- **intended_object**: The open base change isomorphism. For a continuous map f : X → Y and an open V ⊆ Y, it identifies (f_* F)|_V with (f|_{f⁻¹V})_*(F|_{f⁻¹V}), naturally in the sheaf F on X; as functors, i^*_V ∘ f_* ≅ (f_V)_* ∘ i^*_{f⁻¹V}. This comes from the docstring, the module docs and the companion mate lemmas.
- **explanation**: The construction itself is correct. The body:
1. Uses `leftAdjointUniq` to compare Mathlib's `TopCat.Sheaf.pullback` along each open inclusion with the naive pullback `IsOpenEmbedding.sheafPullback`, which is just composition with the image functor on opens.
2. Builds the naive square from `sheafPushforwardContinuousComp`/`Iso` and the equality of opens `preimageOpensIso`.

This gives the standard natural isomorphism (f_*F)|_V ≅ (f_V)_*(F|_{f⁻¹V}).

However, the definition fixes the coefficient category to `Type v`, and no step needs that:
- `leftAdjointUniq`, `sheafPushforwardContinuousComp`/`Iso` and `IsOpenEmbedding.sheafPullback` work for any coefficient category.
- Mathlib's `TopCat.Sheaf.pullback A f` and `pullbackPushforwardAdjunction A f` (Mathlib/Topology/Sheaves/Functors.lean) take any concrete category `A` with `Category.{w} A`, where X, Y : TopCat.{w}. The requirements are limits and colimits, a forgetful functor that preserves limits and filtered colimits, and reflection of isomorphisms. Examples are `AddCommGrpCat.{v}` and `ModuleCat.{v} R`.

So the module's remark that `Type v` is "required by the current `TopCat.Sheaf.pullback` API" is wrong. Only the universe matching is required, not the restriction to `Type`. The textbook statement holds for sheaves with values in any such category. That includes sheaves of abelian groups, which are what this sheaf-cohomology library uses elsewhere (e.g. `pushforward AddCommGrpCat`). The definition should be parametrized by `A`. Mathlib has no ready-made counterpart for this isomorphism.

### [`CategoryTheory.Sheaf.OpenCohomology.restrictToOverCompIso`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/OpenCohomology.lean#L476-L484) — `formal-frontier-0032`

Snippet: `samples/formal-frontier/formal-frontier-0032.lean`

- **verdict**: `too_narrow`
- **intended_object**: The canonical natural isomorphism (F|_U)|_V ≅ F|_V, natural in F, between restricting a sheaf to the over-site of U and then along V ⟶ U, and restricting directly to V. Inferred from the docstring and the name.
- **mathlib_counterpart**: CategoryTheory.Sheaf.pushforwardOverMapIso
- **explanation**: The body is `NatIso.ofComponents (fun F => Sheaf.pushforwardOverMapIso F i)`, with naturality proved by `ext; rfl`. `restrictToOver U` is an abbreviation for `(Opens.grothendieckTopology X).overPullback AddCommGrpCat U`, and `inclusionRestrict i` for `....overMapPullback AddCommGrpCat i`. Mathematically this is the right transitivity isomorphism for restriction.

But `GrothendieckTopology.overPullback`, `GrothendieckTopology.overMapPullback` and `Sheaf.pushforwardOverMapIso` (whose components are identities) are all defined in Mathlib for an arbitrary site (C, J), any coefficient category A and any morphism f : X ⟶ Y. The naturality proof works verbatim in that setting. The construction uses nothing about topological spaces, open sets or AddCommGrpCat, and the sheafification and local-bijectivity hypotheses play no role.

The natural statement is J.overPullback A Y ⋙ J.overMapPullback A f ≅ J.overPullback A X for any site and coefficient category. Mathlib already provides it objectwise as `Sheaf.pushforwardOverMapIso`, together with related coherences such as `overMapPullbackComp`. Specialising to Opens X and abelian-group coefficients is therefore narrower than the construction's natural generality.

### [`AlgebraicGeometry.unitriangularGroupSchemeBaseChangeTowerIso`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularBaseChangeCoherence.lean#L77-L91) — `formal-frontier-0051`

Snippet: `samples/formal-frontier/formal-frontier-0051.lean`

- **verdict**: `too_narrow`
- **intended_object**: For a tower of rings R → S → T, the canonical transitivity-of-base-change isomorphism of group schemes G_T ≅ (G_S)_T. Here G is the unitriangular group scheme U_ι over Spec R. This comes from the docstring ("canonical group-object compositor for pullback over a scalar tower") and from how the iso is used in `unitriangularGroupSchemeBaseChangeIso_tower`.
- **mathlib_counterpart**: CategoryTheory.Over.pullbackComp
- **explanation**: The construction is correct. The body is an `eqToIso` (from `unitriangularBaseMap_comp`), followed by `Functor.mapGrpNatIso (Over.pullbackComp g f)` applied at G, followed by `Functor.mapGrpCompIso` applied at G. This is the canonical isomorphism pullback_{f≫g}(G) ≅ pullback_f(pullback_g(G)) in group objects, so it does define the intended canonical iso.

But the body never uses anything specific to `unitriangularGroupScheme R ι`. The same expression works verbatim for any group object G : Grp (Over (Spec R)). More generally it works for any group object in Over Z of a category with pullbacks, along any composable f, g, where the eqToIso only needs f ≫ g = h. The hypotheses `[Fintype ι] [LinearOrder ι]` and the choice of the unitriangular group serve only to name the object at which the natural isomorphism is evaluated.

Transitivity of base change is a general fact about pullbacks of (group) schemes, and Mathlib supplies it in full generality through `Over.pullbackComp` combined with `Functor.mapGrpNatIso` and `Functor.mapGrpCompIso`. This definition writes that general construction out for one particular group scheme. Its content does not need that special setting, so it is narrower than the natural generality of the notion.

