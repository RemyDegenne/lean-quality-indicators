# Findings

### missing-structure: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L44-L66)

Declaration: `Algebra.TensorProduct.basisAux / basisAux_map_smul / basis`

The isomorphism A ⊗[R] M ≃ (ι →₀ A) is A-linear, and the docstring says so. It is bundled only as an R-linear equiv. The A-linearity is then proved by hand in basisAux_map_smul, using TensorProduct.inductionOn. basis repr is rebuilt with `{ basisAux A b with map_smul' := basisAux_map_smul b }`. The A-linear bundle already exists in the library as Algebra.TensorProduct.equivFinsuppOfBasis, which is `(b.repr.baseChange R A _ _) ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι`. It has an A-linear type and simp lemmas. The file's R-linear definition, the manual A-smul lemma and the `with` repackaging are therefore redundant work.

Proposed change:

Bundle the equivalence as an A-linear equiv, using existing A-linear pieces. For example, define `basis A b := Basis.ofRepr (equivFinsuppOfBasis A b)`, or define basisAux as `b.repr.baseChange R A _ _ ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι` with type `A ⊗[R] M ≃ₗ[A] ι →₀ A`. Delete basisAux_map_smul and the `with` update. Keep basis_repr_tmul and basis_apply as thin simp lemmas, proved from finsuppScalarRight_apply_tmul and finsuppScalarRight_symm_apply_single. To do this, equivFinsuppOfBasis may need generalising from AddCommGroup V and CommSemiring A to AddCommMonoid and Semiring, or the target's typeclass assumptions need aligning with it. I found no import cycle: TensorProduct/Free.lean imports only DirectSum.Finsupp and TensorProduct.Pi.

Benefit: The basis is built from one A-linear equiv. The separate A-smul lemma and the manual structure update go away. The same A-linear equivalence stops being defined twice in Mathlib, with different hypotheses, and readers get the A-linear isomorphism as a public definition.

Source evidence:

- `Algebra.TensorProduct.equivFinsuppOfBasis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Free.lean`: (b.repr.baseChange R A _ _) ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι
- `TensorProduct.finsuppScalarRight` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/DirectSum/Finsupp.lean`: M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M
- `Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: repr := { basisAux A b with map_smul' := basisAux_map_smul b }

### missing-structure: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L151-L152)

Declaration: `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one (and sum_filter_eq_zero_of_mem_Ioo, schwarzChristoffelBoundary_apply_prevertex, tendsto_schwarzChristoffelPrimitive_boundary, schwarzChristoffelBoundary_change_base, continuousOn_schwarzChristoffelBoundary_Icc)`

The 'total exponent at x', defined as the sum of the exponents of all prevertices located at x, is a central mathematical object here. The docstrings call it the 'total exponent' throughout, and it is the exact integrability criterion (> -1) and the vanishing criterion on prevertex-free intervals. It has no name or bundled form. Every statement spells out the raw expression `∑ i with a i = x, e i`. The sum_filter_eq_zero_of_mem_Ioo lemma exists only to recover facts about this function. The same raw expression occurs about 276 times across 46 files of the SchwarzChristoffel directory, for example in Corner/Basic.lean and UnboundedEdge.lean. Hypotheses such as `-1 < ∑ i with a i = x, e i` need a Finset.filter, and a DecidableEq instance on ℝ, in each statement. A rewrite also has to match that syntactic shape. The hypothesis `∀ x ∈ s, -1 < …` is really a statement about the function x ↦ total exponent.

Proposed change:

In Vertex.lean, or at the top of this file, define the total exponent once. A plain `def schwarzChristoffelExponentAt (a e : ι → ℝ) (x : ℝ) : ℝ := ∑ i with a i = x, e i` is enough. A bundled version could instead be the finitely supported function `Finsupp.mapDomain a (Finsupp.equivFunOnFinite.symm e) : ℝ →₀ ℝ`, which is the exponent 'divisor' on the real line. Add a simp lemma `schwarzChristoffelExponentAt_eq_sum`, and a lemma stating that the function vanishes at x when no prevertex of nonzero exponent lies in an interval around x, which is the content of `sum_filter_eq_zero_of_mem_Ioo`. The consumer then becomes `(he : ∀ x ∈ s, -1 < schwarzChristoffelExponentAt a e x)`. The Icc proof reduces to `hp`, `hq`, and the vanishing lemma applied at interior points.

Benefit: Statements become shorter and easier to read, and they match the 'total exponent' wording of the docs. Proofs that handle the exponent at a point (`he`, `hp`, `hq`) no longer depend on a particular Finset.filter spelling. The support of the Finsupp form would give the set of prevertices with nonzero exponent. That set is what the repeated hypothesis `∀ i, e i ≠ 0 → a i ∉ Ioo p q` expresses. Fixing the definition once would also make later changes to it, such as merging coincident prevertices, local to one place.

Source evidence:

- `sum_filter_eq_zero_of_mem_Ioo` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: ∑ i with a i = x, e i = 0
- `Corner/Basic.lean uses the same raw sum in a statement and in the exponent` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Corner/Basic.lean`: (he : -1 < ∑ i with a i = p, e i)
- `Edge.lean repeats the companion interval hypothesis` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)

### missing-structure: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L138-L138)

Declaration: `TauCeti.IsSolidTorusNeighborhood (open solid torus set repeated)`

The open solid torus, the interior of `D² × S¹`, is never named. It is written out as `{p : SolidTorus | ‖(p.1 : ℂ)‖ < 1}` in the structure field and in `closure_setOf_norm_lt_one`, `range_subset_image`, `frontier_image` and `exteriorFrontierHomeomorph`. This file has 6 occurrences and the sibling files have 9 more (`Exterior.lean`, `Link/Basic.lean`, `Link/Exterior.lean`). The boundary torus does have a name (`boundaryInclusion`, `range_boundaryInclusion`), so the two parts of the solid torus are treated asymmetrically. The theorem `closure_setOf_norm_lt_one` is just a lemma about this unnamed set. `knotExterior` and `linkExterior` each re-spell it inside their own definitions.

Proposed change:

Add `def SolidTorus.openPart : Set SolidTorus := {p | ‖(p.1 : ℂ)‖ < 1}` (the name is a suggestion), with `mem_openPart`, `isOpen_openPart` and `closure_openPart` (the current `closure_setOf_norm_lt_one`). Use it in the field `isOpen_image : IsOpen (Φ '' SolidTorus.openPart)`, in `frontier_image`, in `exteriorFrontierHomeomorph`, and in the downstream `knotExterior`/`linkExterior` definitions. Keep `range_boundaryInclusion` as the dual statement. If the `{p | ‖…‖ < 1}` form must stay usable by `simp`, state `mem_openPart` as a `simp` lemma.

Benefit: The definition of `IsSolidTorusNeighborhood`, which is the central notion of the file, would read as 'the image of the open solid torus is open'. The open and boundary parts of the solid torus become symmetric named objects. Downstream files stop duplicating the set-builder and its membership proofs. The openness of the set is proved once, where it is currently re-derived at each use.

Source evidence:

- `knotExterior` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Exterior.lean`: (Φ '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1})ᶜ
- `mem_linkExterior` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Link/Exterior.lean`: x ∈ linkExterior Φ ↔ ∀ i, x ∉ Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1}
- `IsSolidTorusLinkNeighborhood.pairwiseDisjoint_image` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Link/Basic.lean`: Pairwise (Disjoint on fun i => Φ i '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1})

### missing-structure: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L327-L331)

Declaration: `exists_normalDisc`

The docstring says `ψ z` is a 'continuous family of linear isometries onto the normal planes', but the statement uses a bare function `ψ : Circle → ℂ → ℝ³`. It lists the isometry properties as separate conjuncts: `‖ψ z w‖ = ‖w‖`, `Injective (ψ z)`, membership in `normalSubspace`, and surjectivity onto it. Linearity is never stated, and the proof of injectivity is done by hand with `Complex.ext` and `h₁`/`h₂`. Injectivity of an isometry is a standard consequence that Mathlib already supplies for `ℂ →ₗᵢ[ℝ] ℝ³`.

Proposed change:

Produce `ψ : Circle → ℂ →ₗᵢ[ℝ] ℝ³` with `Continuous (fun q : SolidTorus => ψ q.2 q.1)` and `∀ z, LinearMap.range (ψ z).toLinearMap = normalSubspace (𝓡 1) f z`, or the equivalent pointwise range statement. Construct each `ψ z` from the frame `n₁ z, n₂ z` through its coordinates `re` and `im`. The consumer then gets `norm_map` and `LinearIsometry.injective` for free, so the norm and `Injective` conjuncts and the manual `Complex.ext` argument disappear. In `exists_isSolidTorusNeighborhood`, `hnorm` becomes `norm_smul` plus `LinearIsometry.norm_map`. This is a lower-confidence suggestion, since the lemma is private and has a single consumer. The extra `map_add`/`map_smul` proofs partly offset the saving.

Benefit: The linear and isometric structure is exposed in the type instead of being scattered across conjuncts. Injectivity, and possibly the norm computation, come from library lemmas rather than a bespoke proof. The statement matches its own docstring.

Source evidence:

- `exists_normalDisc` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: (∀ w, ‖ψ z w‖ = ‖w‖) ∧ Injective (ψ z) ∧
- `exists_isSolidTorusNeighborhood` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: rw [norm_smul, (hψ q.2).2.1, Real.norm_of_nonneg hr.le]

### missing-structure: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L170-L178)

Declaration: `zero_mem_convexHull_of_best_approx (use of additiveFunction inside the ε-perturbation step)`

`additiveFunction a : Finset U → ℝ` is linear in `a`, but this is not exposed. It is a bare `def` of a sum, with no `LinearMap` or linearity API. To show that scaling the vector `a` by `ε'` scales the value, the proof unfolds the definition and rewrites sums by hand: `simp +decide only [additiveFunction]` at the continuity step, and the long `simp_all ... ← Finset.mul_sum ...` calls in `h_active`. The positive and negative active cases each repeat this. `clm_indicator'_eq_additiveFunction` is another hand-built bridge between the same objects. Pipeline.lean repeats the unfolding for negation and subtraction. These proofs are brittle and obscure the fact that the perturbed term is `f S - ε' * additiveFunction a S`.

Proposed change:

Bundle the map as `additiveFunctionₗ : (U → ℝ) →ₗ[ℝ] (Finset U → ℝ)` and keep `additiveFunction a` as the named operation, with a `@[simp]` lemma `additiveFunctionₗ a S = additiveFunction a S`. Construct it from `fun a S => ∑ i ∈ S, a i`, with `map_add'` from `Finset.sum_add_distrib` and `map_smul'` from `Finset.mul_sum`. If Mathlib's `Finset.sum` pi-linearity API is awkward here, bundle the map explicitly instead. Then `additiveFunction (fun i => ε' * a i) S` becomes `ε' * additiveFunction a S` by `map_smul`. The `h_cont` step reduces to continuity of `ε' ↦ |f S - ε' * c|`, and `h_active` needs no `simp_all` with `← Finset.mul_sum`. The same lemmas would serve the neg/sub cases in Pipeline.lean.

Benefit: The scaling, negation and subtraction steps in this file and in Pipeline.lean stop being repeated unfold-and-simp rewrites. The perturbation argument shows its structure, and the fragile `simp_all` blocks become short rewrites with `map_smul` and `map_neg`.

Source evidence:

- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i
- `key (negation of a in distToAdditive neg lemma)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Pipeline.lean`: simp only [additiveFunction, Finset.sum_neg_distrib]
- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: ← Finset.mul_sum _ _ _,

### missing-structure: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L51-L92)

Declaration: `CKN.Leray.gradientOfCovectorLinear / gradientOfCovectorLinear_norm_bound / gradientOfCovector`

`gradientOfCovector` is built by hand. A plain linear map is defined coordinatewise, then a separate public theorem (about 20 lines of `nlinarith`) proves the crude bound `‖·‖ ≤ 2‖D‖`, and `mkContinuous 2` bundles the two. The map is just the coordinate-evaluation family D ↦ (D (l2BasisVec i))ᵢ with the `PiLp` structure put back on the result. Bundled continuous maps already express this: each `D ↦ D (l2BasisVec i)` is an evaluation CLM, and they can be assembled into a map to `Fin 3 → ℂ` and then into `PiLp 2` via `(PiLp.continuousLinearEquiv 2 ℂ _).symm`. The norm-bound theorem exists only to make this one definition, and it is used nowhere else in the repository.

Proposed change:

Define `gradientOfCovector : (L2Vec3 →L[ℝ] ℂ) →L[ℂ] ComplexVec3` as `(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm ∘L ContinuousLinearMap.pi (fun i => <evaluation at l2BasisVec i as a ℂ-linear CLM on L2Vec3 →L[ℝ] ℂ>)`. Alternatively, since the domain is finite-dimensional, obtain continuity from `LinearMap.toContinuousLinearMap`, so `gradientOfCovectorLinear_norm_bound` and the `mkContinuous` constant 2 disappear. Keep the apply lemma, which is the one consumer `weakTestGradientSchwartz_fourier` needs (`simp [gradientOfCovector, gradientOfCovectorLinear, ...]`). The current proof of that lemma already reduces to a coordinatewise `PiLp.ext`.

Benefit: This removes an ad hoc public norm lemma and its `nlinarith` bookkeeping. The continuity of the gradient extraction then follows from the standard bundled constructors instead of a hand-picked constant. It is also easier to see that the map is just coordinate evaluation.

Source evidence:

- `CKN.Leray.gradientOfCovectorLinear` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: toFun D := WithLp.toLp 2 (fun i => D (l2BasisVec i))
- `ContinuousLinearMap.pi` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/PiProd.lean`: def pi (f : ∀ i, M →L[R] φ i) : M →L[R] ∀ i, φ i where
- `PiLp.continuousLinearEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Normed/Lp/PiLp.lean`: def continuousLinearEquiv : PiLp p β ≃L[𝕜] ∀ i, β i where

### missing-structure: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L305-L317)

Declaration: `pv_cutoff_F_integrable_0_delta (and the sibling private lemmas pv_cutoff_F_integrable_*, pv_cutoff_integral_seg*_eq_*, pv_sector_cutoff_eq)`

The library already has a named bundle for the ε-cutoff PV integrand, `cauchyPrincipalValueIntegrand' f γ z₀ ε`, together with the simp lemmas `_of_gt` and `_of_le`. This file does not use it. Instead, each of about ten private lemmas re-states the same anonymous `let F`/`set F` lambda (lines 309, 326, 344, 374, 402, 445, 474, 495, 521, 546, 584). Each proof then repeats `dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]` or `rw [ite_eq_right (not_lt.mpr _)]` to unfold it by hand. The `pv_sector_cutoff_eq` and `pv_sector_dz_over_z` statements also inline the `if` instead of the named integrand. The sibling file SectorCurveLemma.lean uses `cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε` directly (about 39 uses in the library). As a result, the statements here are not syntactically the same objects that `cauchyPrincipalValue'` and the sibling file refer to.

Proposed change:

State the lemmas with `cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε` in place of the local `F`. Replace each manual `dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left/right …]` with the existing `cauchyPrincipalValueIntegrand'_of_gt` and `cauchyPrincipalValueIntegrand'_of_le`. These need `ε < ‖sectorCurve r α t - 0‖` and `‖…‖ ≤ ε` as hypotheses. State `pv_sector_cutoff_eq` as `∫ t in (0:ℝ)..3, cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε t = I * ↑α`. In `pv_sector_dz_over_z`, `cauchyPrincipalValue'` and `CauchyPrincipalValueExists'` unfold to the same integrand definitionally. The ten-fold `let F` hypothesis blocks can then be dropped.

Benefit: Removes about ten copies of the cutoff-integrand lambda and the repeated unfolding boilerplate. It makes the lemmas here and in SectorCurveLemma.lean about the same named object, so they can be combined without `change`/`simp only [cauchyPrincipalValueIntegrand']` conversions. It also makes explicit that this file works on the library's PV integrand.

Source evidence:

- `cauchyPrincipalValueIntegrand'` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean`: def cauchyPrincipalValueIntegrand' (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0
- `cauchyPrincipalValueIntegrand'_of_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean`: cauchyPrincipalValueIntegrand' f γ z₀ ε t = 0
- `sibling lemma on the sector curve (line 313)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: IntervalIntegrable (cauchyPrincipalValueIntegrand' g (sectorCurve r α) 0 ε)

### missing-structure: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L702-L710)

Declaration: `poitouVerticalProfileSecondDerivative / poitouKernelSecondDerivative (derivative-triple pattern)`

A function and its first and second derivatives are passed as three separate unbundled arguments (f f' f''). The proof that f' and f'' really are derivatives is a separate pair of hypotheses `hf : ∀ x, HasDerivAt f (f' x) x` and `hf' : ∀ x, HasDerivAt f' (f'' x) x`, supplied at every lemma. In the regularized consumers the triple `(regularizedScaledTartar y δ) (regularizedScaledTartarDerivative y δ) (regularizedScaledTartarSecondDerivative y δ)` is retyped dozens of times. Examples are the statement and calc blocks of norm_poitouVerticalProfileSecondDerivative_regularized_le and the Fourier statements near the end of the file. These repeated blocks dominate the statements and make them hard to read.

Proposed change:

Define a small structure for twice-differentiable data, for example `structure TwiceDerivData where f f' f'' : ℝ → ℝ; hf : ∀ x, HasDerivAt f (f' x) x; hf' : ∀ x, HasDerivAt f' (f'' x) x`. Construct one regularized instance `regularizedScaledTartarData y δ` from `hasDerivAt_regularizedScaledTartar` and `hasDerivAt_regularizedScaledTartarDerivative`. Change poitouKernelSecondDerivative and poitouVerticalProfileSecondDerivative to take `(D : TwiceDerivData)`, and keep the named operations as abbreviations. The generic lemmas (hasDerivAt_poitouKernelDerivative, hasDerivAt_poitouVerticalProfileDerivative, abs_poitouKernelSecondDerivative_le) then need no separate derivative hypotheses. The regularized theorems then take `regularizedScaledTartarData y δ` in place of the three-function triple and its two derivative hypotheses. The bundle depends only on definitions already imported here, so it adds no circular dependency.

Benefit: The derivative relationships are checked once, at construction. The long repeated three-function argument lists become a single term. Statements such as the Fourier identities and the integrability and norm bounds become much shorter. Mismatched f/f'/f'' arguments can no longer be written by accident.

Source evidence:

- `hasDerivAt_poitouVerticalProfileDerivative` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:     (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
- `poitouVerticalProfileSecondDerivative_regularized_integrable` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:       (poitouVerticalProfileSecondDerivative
        (regularizedScaledTartar y δ)
        (regularizedScaledTartarDerivative y δ)
        (regularizedScaledTartarSecondDerivative y δ) σ)

### missing-structure: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L64-L68)

Declaration: `smoothPeriodicTestL2`

A smooth periodic test function is passed around as three loose arguments: the function ψ, a smoothness proof hψ, and a periodicity proof hperiodic. Here the periodicity proof is not even used, so it is an unused underscore argument. No bundled object is exposed. Every consumer repeats the pair of hypotheses, and the L² class is applied to the triple. Downstream files each re-prove the same fact about the class (its coeFn is a.e. equal to periodicToTorus ψ): ProductWeakGradient.smoothPeriodicTestL2_coeFn and ScalarFourierDerivative.smoothPeriodicTestL2_ae_periodicToTorus. Each also re-proves its own copy of the smooth-memL2On lemma, using different closed-cell constants. About 22 signatures in the FourierGalerkin directory repeat `(hperiodic : AVenhance.IsZ2Periodic ψ)`.

Proposed change:

Introduce `structure SmoothPeriodicTest where toFun : Vec 2 → ℝ; contDiff : ContDiff ℝ (⊤ : ℕ∞) toFun; periodic : AVenhance.IsZ2Periodic toFun`, with a `CoeFun` instance. It could use `ContDiff ℝ ∞` as the existing code does. Define `SmoothPeriodicTest.toL2 (ψ : SmoothPeriodicTest) : ScalarTorusL2` by the existing `toLp` construction, with `smoothPeriodicTestL2 hψ hperiodic := (⟨ψ, hψ, hperiodic⟩ : SmoothPeriodicTest).toL2` kept as a named wrapper. State `SmoothPeriodicTest.coeFn_toL2 : (fun x : Torus => ψ.toL2 x) =ᵐ[volume] periodicToTorus ψ` once in this file. The consumers then read `weakPathRepresentative_pairing_eq_inner u t (ψ : SmoothPeriodicTest) : ∫ x in unitCube, weakPathRepresentative u t x * ψ x = inner ℝ (u t) ψ.toL2`. `FrozenDriftProblem.initial_pairing_eq_cell_integral` and `weakPathRepresentative_testPairing_continuous` take a single `ψ` too. The `htest`/`hψT` blocks in the proofs are replaced by `ψ.coeFn_toL2`. The bundle could later get a gradient/coordinate-derivative operation, so `productWeakGradient_coord_contDiff` also becomes a constructor.

Benefit: Signatures lose two arguments each, and the repeated hψ/hperiodic pairs disappear. The coeFn lemma is stated once instead of being re-proved in ProductWeakGradient and ScalarFourierDerivative. The unused-periodicity oddity of the definition becomes a documented field. Derivatives and coordinate maps of test functions can then be built as operations on the bundle.

Source evidence:

- `ProductWeakGradient.smoothPeriodicTestL2_coeFn` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/ProductWeakGradient.lean`: theorem ProductWeakGradient.smoothPeriodicTestL2_coeFn {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
- `ScalarFourierDerivative.smoothPeriodicTestL2_ae_periodicToTorus` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/ScalarFourierDerivative.lean`: theorem ScalarFourierDerivative.smoothPeriodicTestL2_ae_periodicToTorus {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) :
- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: inner ℝ (u t) (smoothPeriodicTestL2 hψ hperiodic) := by
  let ψT : ScalarTorusL2 := smoothPeriodicTestL2 hψ hperiodic

### missing-structure: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L340-L347)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent (and its three wrapper theorems)`

Irreducibility of `f` gives a domain structure on the coordinate ring, and so a field structure on the function field. Mathlib's instance search cannot see this, because `planeCurveCoordinateRing_isDomain` is a plain theorem taking `hf`. So each of the four main statements opens with `letI` lines for IsDomain and CharP. Each proof then repeats the same lines as `let : IsDomain ...` and `let : CharP ...`. That is 8 copies in this file (lines 342-343, 364-366, 420-421, 440-442, 468-469, 488-490, 518-519, 536-538). The same `letI := planeCurveCoordinateRing_isDomain hf` header recurs in dozens of statements across the CorvajaZannier directory. Every statement carries a `letI`-prefixed binder, and every proof needs `dsimp only` or an `intro` dance to get past it. The structure `irreducible curve over a field of characteristic p` is not exposed as an instance or a bundle.

Proposed change:

In PlaneCurveFunctionField.lean, expose the structure once. For example, take `[Fact (Irreducible f)]` and declare `instance : IsDomain (PlaneCurveCoordinateRing f)` from `planeCurveCoordinateRing_isDomain Fact.out`. Add a second instance `CharP (PlaneCurveFunctionField f) p` for `[CharP K p]`, derived from `charP_of_injective_algebraMap`. Alternatively, bundle `f` with its irreducibility proof as a structure `IrreducibleCurve K`. The main theorem then reads `theorem planeCurve_auxiliaryFamily_linearIndependent {f} [Fact (Irreducible f)] (hpartialFirst ...) (_hpartialSecond ...) (a b h k : ℕ) ... : LinearIndependent ...`. The `letI` lines, the post-`intro` `let` lines, and the `dsimp only` calls in the wrappers all disappear. Callers use `haveI := Fact.mk hf` instead.

Benefit: Statements shrink by 2-3 lines each and become ordinary universally quantified theorems rather than `letI ... ∀`. The `a b h k` binders can sit before the colon. The wrappers become direct applications instead of `intro`/`apply` scripts. The boilerplate disappears from this file and from the many sibling files that repeat it. Instance data is no longer rebuilt in each proof, which also removes the risk of mismatched instance terms.

Source evidence:

- `planeCurveCoordinateRing_isDomain` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveFunctionField.lean`: theorem planeCurveCoordinateRing_isDomain
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f) :
    IsDomain (PlaneCurveCoordinateRing f)
- `firstCoordinate_transcendental` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveFunctionField.lean`: letI := planeCurveCoordinateRing_isDomain hf
    Transcendental K (planeCurveFunction f 0) := by
  let : IsDomain (PlaneCurveCoordinateRing f) := planeCurveCoordinateRing_isDomain hf
- `secondCoordinate_not_mem_frobeniusSubfield` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/SeparatingCoordinateNotFrobenius.lean`: let : CharP L p := charP_of_injective_algebraMap

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293)

Declaration: `IsBigO.mul_atTop_rpow_of_isBigO_rpow / IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

The two theorems have the same proof, line for line. Both do `refine (hf.mul hg).trans (Eventually.isBigO ?_)` and `filter_upwards [eventually_ge_atTop 1]`. Both then merge `t^a * t^b` into `t^(a+b)` with `rpow_add`, strip the norm with `norm_of_nonneg`, and finish with `rpow_le_rpow_of_exponent_le`. The only difference is a cast step in the `ℕ` version. The pointwise analytic inequality `‖t^a * t^b‖ ≤ t^c` for `1 ≤ t` and `a + b ≤ c` is therefore written out twice. Any change to it, such as the norm form or the `rpow_add` side conditions, has to be made in both places.

Proposed change:

Add a private (or public) lemma with the core pointwise inequality, e.g.
`lemma norm_rpow_mul_rpow_le_rpow {a b c t : ℝ} (ht : 1 ≤ t) (h : a + b ≤ c) : ‖t ^ a * t ^ b‖ ≤ t ^ c`.
Proof sketch: `rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _)]; exact Real.rpow_le_rpow_of_exponent_le ht h`.
The real-variable theorem then becomes `(hf.mul hg).trans (Eventually.isBigO (by filter_upwards [eventually_ge_atTop 1] with t ht; exact norm_rpow_mul_rpow_le_rpow ht h))`.
The `ℕ` theorem is the same with `exact norm_rpow_mul_rpow_le_rpow (Nat.one_le_cast.mpr ht) h`.
Both keep their current hypotheses (`SeminormedRing E`, `atTop`), and the lemma needs no new imports.

Benefit: The analytic argument is stated and maintained once. Each theorem shrinks to the filter and cast plumbing that actually differs between them, so a reader can see that the `ℕ` version is the `ℝ` version transported along the cast.

Source evidence:

- `IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
- `IsBigO.mul_atTop_rpow_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: exact Real.rpow_le_rpow_of_exponent_le ht h

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L185-L206)

Declaration: `Complex.isBigO_cpow_rpow / Complex.isTheta_cpow_rpow`

Both calc proofs end with the same two steps. They divide `‖f x‖ ^ (g x).re` by `Real.exp (arg (f x) * im (g x))`, replace that denominator by `1` via `isTheta_exp_arg_mul_im`, and then simplify with `div_one`. Only the first step differs: `isBigO_of_le` with `norm_cpow_le` versus `of_norm_eventuallyEq` with `norm_cpow_of_imp`. The `isBigO` version needs extra `show α → ℝ from` annotations to elaborate the same chain.

Proposed change:

Factor out `lemma isTheta_norm_rpow_div_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) : (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) =Θ[l] fun x => ‖f x‖ ^ (g x).re`.
Proof sketch: `((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl)).trans_eventuallyEq (by simp only [div_one, EventuallyEq.rfl])`, or the existing calc steps.
Then `isBigO_cpow_rpow` is `(isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)).trans_isTheta (isTheta_norm_rpow_div_exp_arg_mul_im hl)`.
`isTheta_cpow_rpow` is `(.of_norm_eventuallyEq <| hl.mono fun _ => norm_cpow_of_imp).trans (isTheta_norm_rpow_div_exp_arg_mul_im hl_im)`.
The hypotheses `hl` and `hl_im` are unchanged.

Benefit: Each theorem then shows only what distinguishes it: the one-sided bound versus the two-sided equivalence, and the extra non-vanishing hypothesis. The shared 'the exp factor is bounded above and below' reduction is stated once. This removes the `show α → ℝ from` clutter and the duplicated calc tail.

Source evidence:

- `Complex.isBigO_cpow_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl))
- `Complex.isTheta_cpow_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L323)

Declaration: `Bundle.Trivialization.mk_coordChangeL and VectorPrebundle.mk_coordChange`

The two theorems have the same first-component proof. It is a roundabout computation: it rewrites `e.symm` through `mk_symm` and `proj_symm_apply'` just to show the first component of `e' ⟨b, _⟩` is `b`. The goal only needs `(e' x).1 = proj x` for `x = ⟨b, e.symm b y⟩` with `b ∈ e'.baseSet`. That is exactly the existing lemma `mk_proj_snd'`. `e` and `e.symm` play no role, so the file maintains the same non-trivial block twice, once for `Trivialization` (lines 319–322) and once for `Pretrivialization` (lines 862–865, in `VectorPrebundle.mk_coordChange`). The second component, `coordChangeL_apply` or `coordChange_apply`, is the only part that differs.

Proposed change:

Replace the first bullet of each proof with the existing lemma. For `mk_coordChangeL`: `rw [e.coordChangeL_apply e' hb y]; exact e'.mk_proj_snd' (x := ⟨b, e.symm b y⟩) hb.2`. For `VectorPrebundle.mk_coordChange`: `rw [a.coordChange_apply he he' hb v]; exact e'.mk_proj_snd' (x := ⟨b, e.symm b v⟩) hb.2`. In the first, `e'.mk_proj_snd'` is the `Trivialization` version. In the second it is the `Pretrivialization` version. The rewrite turns the left side into `(b, (e' ⟨b, _⟩).2)`, and `proj ⟨b, _⟩` reduces to `b` by `rfl`. No new helper is needed. Alternatively, `Prod.ext (e'.coe_fst' hb.2).symm (coordChangeL_apply ..)` also works. This removes the four-line `mk_symm`/`proj_symm_apply'` block from both places.

Benefit: The duplicated proof, which needs `e.mk_symm` and `proj_symm_apply'` twice, becomes a one-line appeal to a named lemma in both places. A reader sees that only `e'` and `b ∈ e'.baseSet` matter, and any change to the argument is made once in the library lemma.

Source evidence:

- `VectorPrebundle.mk_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
- `Bundle.Pretrivialization.mk_proj_snd'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean`: theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L275-L292)

Declaration: `Bundle.Trivialization.coordChangeL (continuous_toFun / continuous_invFun fields)`

The `continuous_toFun` and `continuous_invFun` fields are the same continuity argument with `e` and `e'` swapped, each followed by an identical `dite_eq_right`/`continuous_id` branch. Both prove that `y ↦ (e' ⟨b, e.symm b y⟩).2` is continuous, via the composition `e'.continuousOn ∘ e.continuousOn_symm ∘ (b, ·)`. That statement is already proved for arbitrary trivializations as `Trivialization.continuous_coordChange` (`Continuous (e₁.coordChange e₂ b)`). So the file reproduces the same non-trivial topological reasoning twice, and again duplicates an existing library proof.

Proposed change:

In the positive branch of `continuous_toFun`, use `Trivialization.continuous_coordChange` applied to `e`, `e'`, `hb.1`, `hb.2`. Close the goal by matching the coordinates pointwise. For `y`, the coercion of `(e.linearEquivAt R b _).symm.trans (e'.linearEquivAt R b _)` is `(e' ⟨b, e.symm b y⟩).2`. Rewriting with `e.mk_symm hb.1 y` turns that into `e.coordChange e' b y`, which is its definition. In `continuous_invFun`, apply the same lemma to `e'` and `e` with `hb.2`, `hb.1`. Alternatively, factor out one local `have` stating `∀ (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] {b}, b ∈ e.baseSet → b ∈ e'.baseSet → Continuous fun y => (e' ⟨b, e.symm b y⟩).2`, and use it twice. Either way, only the `by_cases` and `continuous_id` scaffolding remains duplicated.

Benefit: The mirrored 8-line blocks shrink to short appeals to one continuity statement. The symmetry of the two fields becomes explicit. A change to the continuity argument, such as the `prodMk_right` and `mk_mem_prod` plumbing, is made in one place, and the file reuses Mathlib's `coordChange` machinery instead of re-deriving it.

Source evidence:

- `Bundle.Trivialization.continuous_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean`: theorem continuous_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) : Continuous (e₁.coordChange e₂ b)
- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
- `Bundle.Trivialization.coordChangeL_apply'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: coordChangeL R e e' b y = (e' (e.toOpenPartialHomeomorph.symm (b, y))).2

### repeated-proof-machinery: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L199-L259)

Declaration: `continuousOn_schwarzChristoffelBoundary / schwarzChristoffelBoundary_sub_eq / schwarzChristoffelBoundary_injOn / collinear_schwarzChristoffelBoundary_image`

Four theorems each obtain `L` from an Edge lemma together with `hL : ∀ x ∈ Ioo p q, Tendsto … (𝓝 (L x))`. Each then re-applies `schwarzChristoffelBoundary_eq_of_tendsto … (hL x hx)` pointwise to replace the boundary map by `L`. The collinear proof does this twice, once in each direction of a hand-written `ext z` set-equality. The repeated step is 'the boundary map equals `L` on the interval, so transfer continuity, injectivity, increments and image collinearity'. It is rederived in each proof, with ad hoc `rw`/`convert`/`ext`.

Proposed change:

Add one lemma next to `schwarzChristoffelBoundary_eq_of_tendsto`:

theorem schwarzChristoffelBoundary_eqOn_of_tendsto (a e : ι → ℝ) (z₀ : UpperHalfPlane) {s : Set ℝ} {L : ℝ → ℂ} (hL : ∀ x ∈ s, Tendsto (schwarzChristoffelPrimitive a e z₀) (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 (L x))) : EqOn (schwarzChristoffelBoundary a e z₀) L s := fun x hx => schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)

The proof is one line from the existing lemma. Then rewrite each use with `h := schwarzChristoffelBoundary_eqOn_of_tendsto a e z₀ hL`:
- `continuousOn_schwarzChristoffelBoundary`: `hLcont.congr h`.
- `schwarzChristoffelBoundary_injOn`: `hLinj.congr h.symm`. This needs `Set.InjOn.congr` with the right direction of `EqOn`.
- `collinear_schwarzChristoffelBoundary_image`: `rwa [h.image_eq]`, or `h.image_eq ▸ hLcol`, replacing the `convert`/`ext`/`constructor` block.
- `schwarzChristoffelBoundary_sub_eq`: `rw [h hx, h hy]; exact hsub x hx y hy`.

The hypotheses and imports are unchanged. `hL` has exactly the shape the two Edge lemmas return.

Benefit: The collinear proof loses its manual set-extensionality argument, and the injectivity and continuity proofs lose their per-point rewriting. All four proofs then use a single statement of the identification 'boundary = L on the edge'. A change to how the boundary is identified with the edge limit function would then be made in one place.

Source evidence:

- `collinear_schwarzChristoffelBoundary_image` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:   · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)).symm⟩
- `exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: InjOn L (Ioo p q) ∧ Collinear ℝ (L '' Ioo p q)

### repeated-proof-machinery: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L91-L102)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`

The proof builds the hypotheses `hβγ`/`hγα` for the triple (γ, -α, β), applies the cyclic Killing-form symmetry to it, and then applies skew-symmetry `N(γ,-α) = -N(-α,γ)`. `structureConstant_neg_add_mul_killingForm_eq` in Normalization.lean (lines 103-113) repeats this exact derivation: the same two coordinate equations, the same `structureConstant_mul_killingForm_eq γ (-α) β` call, and the same `structureConstant_skew (-α) γ β`. That lemma only adds the Chevalley-involution rewrite `hneg`. The unconditional core is `N(-α,-β)·B(γ) = -N(-α,γ)·B(β)`. It is proved twice, once with and once without the involution hypothesis, and the Chevalley version re-derives it instead of reusing it.

Proposed change:

Add one lemma to Symmetry.lean, where `structureConstant_mul_killingForm_eq` and `structureConstant_skew` are already available. Its statement: `hx.structureConstant (-α) (-β) (-γ) hγ.neg _ * killingForm K L (x γ) (x (-γ)) = -(hx.structureConstant (-α) γ β hβ _ * killingForm K L (x β) (x (-β)))`, under `hβ hγ hαβ`. Proof: introduce `hγα` and `hαγ` by `rw [Weight.coe_neg, hαβ]; abel`, then `have := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ; rw [hx.structureConstant_skew (-α) γ β hβ hαγ] at this; linarith`, with `neg_mul` used to normalise. In Opposite.lean, replace `hβγ/hγα/hcyc/hskew` and the `rw [hcyc]`/`rw [hskew]` calc steps by this lemma. The chain becomes `N·(N'·Bγ) = N·(-(N(-α,γ)·Bβ)) = -(N·N(-α,γ))·Bβ`, followed by the existing `hprod`. In Normalization.lean, `structureConstant_neg_add_mul_killingForm_eq` reduces to `have h := <new lemma>; rw [hneg] at h; simpa only [neg_mul, neg_inj] using h`.

Benefit: The cyclic-plus-skew reduction is proved once as an unconditional fact. Each caller states only what it adds: the product formula here, the involution rewrite there. A change to the weight-equation bookkeeping or to the shape of the cyclic lemma then needs one edit instead of two parallel ones. The Chevalley version shows plainly that it specialises the unconditional identity.

Source evidence:

- `TauCeti.IsSl2System.structureConstant_neg_add_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: have hcyclic := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ
- `TauCeti.IsSl2System.structureConstant_neg_add_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: have hskew := hx.structureConstant_skew (-α) γ β hβ hαγ
- `TauCeti.IsSl2System.structureConstant_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean`: hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =
      hx.structureConstant β (-γ) (-α) hα.neg

### repeated-proof-machinery: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L103-L108)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`

This proof and `structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` (Normalization.lean 163-179) share the same final stage. Each proves `B(γ, -γ) ≠ 0` with the same four-argument call to `killingForm_ne_zero_of_mem_rootSpace`, and each cancels it with `mul_right_cancel₀`. Each then moves the factor `(q·(p+1) : ℕ)·B(β)` through the length-ratio hypothesis to `(p+1)²·B(γ)`, by `push_cast; ring`, then `rw [hlength]`, then `ring`. The same non-vanishing proof is also repeated in FourTerm.lean and Involution.lean. Here the ratio step is written out as the calc steps at lines 124-131. The ratio computation is the nontrivial part: `q·B(β) = (p+1)·B(γ)` implies `q(p+1)·B(β) = (p+1)²·B(γ)`.

Proposed change:

Add two small lemmas next to the Killing-form API in Symmetry.lean. First, `killingForm_root_neg_ne_zero (hx) (γ) (hγ) : killingForm K L (x γ) (x (-γ)) ≠ 0`, with the existing `killingForm_ne_zero_of_mem_rootSpace` proof as its body. Second, `chainTopCoeff_mul_chainBotCoeff_succ_mul_killingForm_eq`, giving `((q * (p+1) : ℕ) : K) * B(β) = ((p+1 : ℕ) : K)^2 * B(γ)` from `hlen`. Its proof is `push_cast; linear_combination (↑(p+1)) * hlen`, with the cast shape adjusted to fit. Opposite.lean then needs only `apply mul_right_cancel₀ (hx.killingForm_root_neg_ne_zero γ hγ)` and one rewrite with the second lemma. The ratio-specific calc steps (`push_cast; ring`, `rw [hlen]`, `ring`) are removed. Normalization.lean's `…_of_killingForm_ratio` is shortened the same way.

Benefit: The conclusion `…·B(γ) = -(p+1)²·B(γ)` follows from `hprod` and one named lemma, so the root-length step is no longer buried in an eight-line calc. The same lemma serves both the product identity and the Chevalley square identity. The non-vanishing proof stops being copied across four files.

Source evidence:

- `TauCeti.IsSl2System.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: killingForm_ne_zero_of_mem_rootSpace hγ (hx.mem_rootSpace γ) (hx.ne_zero γ hγ)
      (hx.mem_rootSpace (-γ)) (hx.ne_zero (-γ) hγ.neg)
- `TauCeti.IsSl2System.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: ((chainBotCoeff α β + 1 : ℕ) : K) *
        ((chainTopCoeff α β : K) * killingForm K L (x β) (x (-β))) := by
          push_cast
          ring
- `(FourTerm.lean, nonvanishing step)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/FourTerm.lean`: killingForm_ne_zero_of_mem_rootSpace hμ (hx.mem_rootSpace μ) (hx.ne_zero μ hμ)

### repeated-proof-machinery: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L190-L248)

Declaration: `zero_mem_convexHull_of_best_approx (inner h_active, both by_cases branches)`

The two branches of `h_active` prove the same fact. If `|f S| = M` and `f S * additiveFunction a S > 0`, then `|f S - ε * additiveFunction a S| < M` for small `ε > 0`. The positive branch handles `f S = M` and `additiveFunction a S > 0`. The negative branch handles `f S = -M` and `additiveFunction a S < 0`. Each branch repeats the same steps. It unfolds `additiveFunction` with a long `simp_all` list. It pulls `ε'` out of the sum with `← Finset.mul_sum`. It picks the witness `M / |s|` (written as `M / (-∑ …)` or `M / ∑ …`). It splits `abs_lt` and closes both sides with `nlinarith [mul_div_cancel₀ …]`. The two simp sets differ only by `abs_neg` versus `abs_eq_self`. The proofs depend on `simp_all` normal forms, so they are brittle. The witness is written in terms of `Λ`, so the sign case-split has leaked into the choice of `ε`.

Proposed change:

Add a standalone real-number lemma and use it in both branches.

`lemma exists_small_eps_abs_sub_lt {x s M : ℝ} (hM : 0 < M) (hx : |x| = M) (hxs : 0 < x * s) : ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, |x - ε * s| < M`

Proof sketch:
1. Here `s ≠ 0`. Take `δ = M / |s|`, so `ε * |s| < M` for `ε ∈ Ioo 0 δ`.
2. Since `x = ±M`, either `x = M` with `s > 0` or `x = -M` with `s < 0`, so `x - ε s` is `x` shrunk toward 0 by `ε |s| < M`.
3. Hence `-M < x - ε s < M` by `abs_lt` and `nlinarith`. Alternatively, case-split once on `eq_or_eq_neg_of_abs_eq hx` inside this lemma, so the case split happens only there.

Rewritten `h_active`:
`intro S hS`
`have hs : 0 < f S * additiveFunction a S := by rcases eq_or_eq_neg_of_abs_eq hS with h | h <;> simp [h, h_additiveFunction_a_pos S, h_additiveFunction_a_neg S, hM_pos]` (the tactic details need adjusting).
`obtain ⟨δ, hδ, h⟩ := exists_small_eps_abs_sub_lt hM_pos hS hs`
`refine ⟨δ, hδ, fun ε' hε' => ?_⟩`
`simpa [additiveFunction, ← Finset.mul_sum, ha_def] using h ε' hε'`

The rewrite keeps the hypotheses used today: `hM_pos`, `hS : |f S| = M`, and the two sign facts `h_additiveFunction_a_pos` and `h_additiveFunction_a_neg`. It needs no new imports. The lemma only needs `Mathlib.Analysis.SpecialFunctions.Pow.Real` and ordered-field facts already available. If preferred, `h_inactive` could be folded into the same helper by taking `|x| ≤ M` and handling `|x| < M` by continuity.

Benefit: The two ~28-line `simp_all`/`nlinarith` blocks become one small, stable real-variable lemma and one short derivation. The sign symmetry is proved once, outside the Hahn–Banach context. A reader can see why `ε` exists without checking that the second branch mirrors the first. Maintenance gets easier, because a change to `additiveFunction` or to the shape of the perturbation no longer requires editing two fragile `simp_all` normal forms.

Source evidence:

- `zero_mem_convexHull_of_best_approx (positive branch)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: ⟨M / (-∑ i ∈ S, Λ (Function.update 0 i 1)),
            div_pos hM_pos (neg_pos.mpr (h_additiveFunction_a_pos S hS_pos)),
- `zero_mem_convexHull_of_best_approx (negative branch)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: nlinarith [
                    mul_div_cancel₀ M (ne_of_gt (h_additiveFunction_a_neg S hS_neg))]
- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L368-L415)

Declaration: `realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree (and the wrappers realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree)`

The two *Representative theorems repeat the same argument. Each one applies realPart_isWeakDivFree_of_fourierOrthogonal. Each one then rewrites ℱ(ℱ.symm (multiplier …)) back to the multiplier with apply_symm_apply. Each one turns the equality in Lp into an a.e. equality with Lp.ext_iff. Finally each runs filter_upwards [htransformAE, <multiplier>_divergence_free_ae …] and closes with rw [hξ]; exact hrange. The two wrapper theorems (realLerayProjection_isWeakDivFree and realStokesOperator_isWeakDivFree) repeat a second argument. Both set z, obtain hRange and hAE := realPartVectorL2Representative_eq_ae z, change the goal to the realPartVectorL2 form, and apply isWeakDivFree_congr_ae hAE.symm hRange. Only the operator differs.

Proposed change:

Add two helpers before the concrete theorems.

(1) `theorem realPart_isWeakDivFree_of_fourier_eq_ae (v w : ComplexVectorL2) (hvw : MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v = w) (hw : ∀ᵐ ξ ∂volume, inner ℂ (complexifyFrequency ξ) (w ξ) = 0) : CKN.IsWeakDivFreeL2 (realPartVectorL2Representative v)`.
Proof sketch: `apply realPart_isWeakDivFree_of_fourierOrthogonal; filter_upwards [(Lp.ext_iff).mp hvw, hw] with ξ h1 h2; rw [h1]; exact h2`.

(2) `theorem realPartVectorL2_isWeakDivFree_of_representative (z : ComplexVectorL2) (h : CKN.IsWeakDivFreeL2 (realPartVectorL2Representative z)) : CKN.IsWeakDivFreeL2 (realVectorL2Representative (realPartVectorL2 z))`.
Proof sketch: `exact isWeakDivFree_congr_ae (realPartVectorL2Representative_eq_ae z).symm h`.

The Leray use is then `realPart_isWeakDivFree_of_fourier_eq_ae _ (lerayFourierMultiplier (ℱ (complexifyVectorL2 f))) (ℱ.apply_symm_apply _) (lerayFourierMultiplier_divergence_free_ae _)`. Here ℱ.apply_symm_apply _ is the existing `change ℱ (ℱ.symm …) = _` step. It should unify because lerayProjectionL2 unfolds to ℱ.symm (lerayFourierMultiplier (ℱ v)). The Stokes use has the same shape with stokesFourierMultiplier ht (ℱT …), ℱV.apply_symm_apply _ and stokesFourierMultiplier_divergence_free_ae ht _. The two non-Representative theorems become `realPartVectorL2_isWeakDivFree_of_representative _ (realLerayProjectionRepresentative_isWeakDivFree f)` and the Stokes analogue.

Benefit: Each concrete theorem shrinks from about 12 lines to a one- or two-line application. A future multiplier with divergence-free range (another Fourier multiplier operator) can reuse the helpers instead of copying the htransform / Lp.ext_iff / filter_upwards pattern. The argument that a Fourier multiplier with orthogonal range gives a weakly divergence-free real part is stated once.

Source evidence:

- `realStokesOperatorRepresentative_isWeakDivFree` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: stokesFourierMultiplier_divergence_free_ae ht
      (ℱT (complexifyTensorL2 F))] with ξ hξ hrange
  rw [hξ]
  exact hrange
- `lerayProjectionL2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean`: exact ℱ.symm (lerayFourierMultiplier (ℱ v))
- `stokesL2Operator` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierLeray.lean`: exact ℱV.symm (stokesFourierMultiplier ht (ℱT F))
- `realStokesOperator` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierRealification.lean`: fun F => realPartVectorL2 (stokesL2Operator ht (complexifyTensorL2 F))

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L504-L513)

Declaration: `pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta and pv_cutoff_integral_seg1_eq_inv / pv_cutoff_integral_seg2_eq_Ialpha / pv_cutoff_integral_seg3_eq_neg_inv`

The pointwise evaluation of the cutoff integrand F on each open segment is proved twice. The first copy is `h_eq` inside the integrability lemmas (lines 358–363, 380–390, 412–425). The second is `h_on_Ioo` inside the integral-equality lemmas (lines 504–513, 526–536, 557–570). For segment 2 the two blocks are line-for-line identical. For segments 1 and 3 they differ only in how the first branch is closed. In each, the case split on `ite` is done by hand, `sectorCurve_seg*` and `deriv_sectorCurve_seg*` are rewritten, and `field_simp` is called with side conditions. The file already has `pv_integrand_seg1/2/3` (lines 213–245) and `sectorCurve_norm_on_arc`, which state the same computation. The integrability lemmas use `pv_integrand_seg1` in the segment 1 case but not in segments 2 or 3. The integral lemmas use none of them. The `ε = δ * r < t * r` calc for the norm bound is also copied three times, at lines 361–363, 511–513 and 568–570.

Proposed change:

Add three private lemmas giving the value of F on each open segment, with the `ite` split and norm estimate done once. For example:
`lemma cutoff_eq_inv_on_seg1 (hr : 0<r) (hε : 0<ε) {t} (ht : t ∈ Ioo (ε/r) 1) : (if ‖sectorCurve r α t - 0‖ > ε then (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t else 0) = ↑(t⁻¹)`.
There is an analogous lemma for `Ioo 1 2` with value `I*↑α` (it needs `ε < r`), and one for `Ioo 2 (3-ε/r)` with value `-↑((3-t)⁻¹)`.
Proof sketch: `rw [if_pos]`, then `simp only [sub_zero]` and apply `pv_integrand_seg1/2/3`. The guard `ε < ‖γ t‖` comes from `sectorCurve_norm_seg1`, `sectorCurve_norm_on_arc` or `sectorCurve_norm_seg3'` together with `ε = (ε/r)*r < t*r`.
Then replace the six `h_eq` / `h_on_Ioo` blocks by one-line uses. For the integrals, `intervalIntegral.integral_congr_Ioo_of_le hδ1.le (fun t ht => lemma ... ht)` replaces the manual `integral_congr_ae` plumbing. For integrability, `IntervalIntegrable.congr_uIoo` (or `intervalIntegrable_congr`) applies directly to the continuous or constant comparison function.

Benefit: The roughly 15-line evaluation argument for each segment is stated and proved once instead of twice. The `pv_integrand_seg*` lemmas are actually reused instead of being re-derived inline. If the definition of the cutoff integrand changes (for example a non-strict inequality, or a different centre than `0`), only three lemmas need repair, not six large blocks.

Source evidence:

- `pv_integrand_seg2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem pv_integrand_seg2 (r : ℝ) (hr : 0 < r) (α : ℝ) (t : ℝ) (ht : t ∈ Ioo 1 2) :
    (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α
- `pv_cutoff_F_integrable_1_2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have : exp (I * ↑((t - 1) * α)) ≠ 0 := Complex.exp_ne_zero _
      field_simp
- `intervalIntegral.integral_congr_Ioo_of_le` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`: theorem integral_congr_Ioo_of_le [NullSingletonClass μ] (hab : a ≤ b) (h : (Ioo a b).EqOn f g) :
- `IntervalIntegrable.congr_uIoo` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`: theorem IntervalIntegrable.congr_uIoo [NullSingletonClass μ] {g : ℝ → ε}
    (hf : IntervalIntegrable f μ a b) (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ a b

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L364-L370)

Declaration: `pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta (a.e. transfer from Ioo to integrability) and pv_cutoff_integral_seg*_eq_* (a.e. transfer for integral equality)`

The same measure-theoretic transfer from the open interval to the interval integral is hand-written six times. Three copies handle integrability (lines 364–370, 391–398, 434–441): restrict the comparison function to `Ioo`, use `Integrable.congr` with `ae_restrict_mem`, then rewrite with `Measure.restrict_congr_set Ioo_ae_eq_Ioc`. Three copies handle integral equality (lines 514–517, 537–542, 571–574): `filter_upwards [Filter.eventuallyEqSet_iff.mp Ioo_ae_eq_Ioc]`, then `Set.uIoc_of_le`, then `ht.mpr`. Mathlib already provides this as `IntervalIntegrable.congr_uIoo`, `intervalIntegrable_congr_uIoo` and `intervalIntegral.integral_congr_Ioo_of_le`, so this boilerplate is not needed in either case.

Proposed change:

Together with the segment-evaluation lemmas of the previous finding, rewrite each integrability lemma as a continuity or constant fact about the comparison function, followed by `(hg : IntervalIntegrable g volume a b).congr_uIoo (fun t ht => (heq t (by rwa [Set.uIoo_of_le hab] at ht)).symm)`. Rewrite each integral lemma as `intervalIntegral.integral_congr_Ioo_of_le hab heq`. For segment 2 the comparison function is the constant `I*↑α`, so integrability is `intervalIntegrable_const`, and the integral is `integral_const` with a `simp`. This removes about 40 lines of repeated a.e. plumbing.

Benefit: Each lemma reduces to its mathematical content (the continuity of `1/t` or `-1/(3-t)` away from the pole, the value of the constant on the arc), with no distracting measure-theory boilerplate. The proofs also no longer depend on `Ioo_ae_eq_Ioc` rewriting, which is fragile.

Source evidence:

- `pv_cutoff_integral_seg3_eq_neg_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: filter_upwards [(Filter.eventuallyEqSet_iff.mp Ioo_ae_eq_Ioc)] with t ht
  rw [Set.uIoc_of_le (le_of_lt h3δ)]
  exact fun ht_mem => h_on_Ioo t (ht.mpr ht_mem)
- `intervalIntegral.integral_congr_Ioo_of_le` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`: theorem integral_congr_Ioo_of_le [NullSingletonClass μ] (hab : a ≤ b) (h : (Ioo a b).EqOn f g) :
    ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
- `IntervalIntegrable.congr_uIoo` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`: theorem IntervalIntegrable.congr_uIoo [NullSingletonClass μ] {g : ℝ → ε}
    (hf : IntervalIntegrable f μ a b) (h : EqOn f g (uIoo a b)) : IntervalIntegrable g μ a b

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593-L610)

Declaration: `pv_cutoff_F_integrable_0_delta / pv_cutoff_F_integrable_3delta_3 and the hI1 / hI5 blocks of pv_sector_cutoff_eq`

The fact that F vanishes in the cutoff neighbourhoods of the endpoints is proved twice for each end. For the left end, the integrability lemma `pv_cutoff_F_integrable_0_delta` (lines 317–322) and `hI1` (lines 593–601) both unfold F, apply `ite_eq_right (not_lt.mpr _)`, rewrite with `sectorCurve_norm_seg1`, and bound `t*r ≤ δ*r = ε`. For the right end, `pv_cutoff_F_integrable_3delta_3` (lines 334–340) and `hI5` (lines 602–610) do the same with `sectorCurve_norm_seg3'`. The two conclusions (`IntervalIntegrable F ... 0 δ` and `∫ F = 0`) both follow from the single statement 'F = 0 on the interval'.

Proposed change:

State two private lemmas, `cutoff_eq_zero_near_start : t ∈ Icc 0 (ε/r) → F t = 0` and `cutoff_eq_zero_near_end : t ∈ Icc (3-ε/r) 3 → F t = 0`. Each proof is the existing `ite_eq_right` / `sectorCurve_norm_seg*` / `field_simp` argument, written once. Then `pv_cutoff_F_integrable_0_delta` becomes `(intervalIntegrable_const (c := 0)).congr (fun t ht => (cutoff_eq_zero_near_start ... ).symm)`, using `intervalIntegrable_congr` on `Ι 0 δ ⊆ uIcc`. Likewise `hI1` becomes `(intervalIntegral.integral_congr (fun t ht => ...)).trans intervalIntegral.integral_zero`. The same applies on the right end.

Benefit: The norm estimates near the origin are stated once. The integrability proof and the value of the integral then visibly rely on the same fact, and any change to the cutoff form needs one edit per end instead of two.

Source evidence:

- `pv_cutoff_F_integrable_0_delta` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
  exact le_trans (mul_le_mul_of_nonneg_right ht.2 hr.le)
    (le_of_eq (by rw [hδ_def]; field_simp))
- `pv_cutoff_F_integrable_3delta_3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
  have : (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L291-L297)

Declaration: `log_cancellation (duplicates integral_seg1_eq_neg_log / integral_seg3_eq_log)`

The substitution `u = 3 - t` that turns the segment-3 log integral into the segment-1 one is proved in `integral_seg3_eq_log` (lines 259–268) and then reproved verbatim in `log_cancellation` with `ε / r` in place of `ε`, including the `integral_comp_sub_left` plus `congr 1 <;> ring` step. The earlier lemmas `integral_seg1_eq_neg_log` and `integral_seg3_eq_log` state exactly the needed facts for `ε := ε / r`, but `log_cancellation` re-derives them (h1 via `integral_inv_of_pos` and `Real.log_div`, h2 via the copied block), so those two lemmas are not used there.

Proposed change:

Reuse the existing lemmas with `ε / r`, which is positive and less than 1, so `integral_seg1_eq_neg_log (ε/r) hεr_pos hεr_lt1` and `integral_seg3_eq_log (ε/r) hεr_pos hεr_lt1` give `h1` and `h2` directly. Then only the cast bookkeeping `h1c`, `h2c` and the final `Complex.ofReal_add` step remain. If preferred, extract the real-variable cancellation `(∫ t in a..1, t⁻¹) + (∫ t in 2..3-a, -(3-t)⁻¹) = 0` for `0<a<1`, and cast to ℂ once with `intervalIntegral.integral_ofReal`.

Benefit: The `u = 3 - t` substitution is proved once. `log_cancellation` shrinks by about a dozen lines to the complex-cast step, and the two real-variable lemmas have a use.

Source evidence:

- `integral_seg3_eq_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h1 : ∫ t in (2 : ℝ)..(3 - ε), (3 - t)⁻¹ = ∫ u in ε..1, u⁻¹ := by
    have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
      (a := (2 : ℝ)) (b := 3 - ε)
- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428)

Declaration: `norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le`

The two norm bounds repeat the same analytic reduction. (1) Each proves the phase bound exp((σ-1/2)x) ≤ exp(a|x|) from le_abs_self (lines 356 and 976). (2) Each simp-normalises ‖(real) * exp(...)‖ into |·| * exp((σ-1/2)x), with the same simp set and the same hnorm fact for ‖(σ:ℂ)-1/2‖ (about lines 385 and 1037). (3) Each multiplies by the Gaussian bound and merges exp(-δx²)·exp(a|x|) = exp(-δx²+a|x|) via Real.exp_add and ring. (4) Each closes with exp_neg_mul_sq_add_mul_le hδ a x (lines 427 and 1132). The second proof, about 100 lines, also re-derives the nonnegativity of the polynomial factor twice (hP, then again inside the last calc step). Only the polynomial prefactor differs between the two proofs.

Proposed change:

Add one lemma after abs_poitouKernel_regularizedScaledTartar_le_gaussian:

theorem norm_mul_exp_phase_le_of_norm_le_gaussian {δ : ℝ} (hδ : 0 < δ) (σ x P : ℝ) (hP : 0 ≤ P) (z : ℂ) (hz : ‖z‖ ≤ P * Real.exp (-δ * x ^ 2)) : ‖z * Complex.exp ((σ - 1 / 2) * x)‖ ≤ Real.exp (|σ - 1 / 2| ^ 2 / (2 * δ)) * (P * Real.exp (-(δ / 2) * x ^ 2)).

Proof sketch: use norm_mul and Complex.norm_exp to get ‖z‖ * Real.exp ((σ-1/2)x). Bound the exponential by Real.exp (|σ-1/2| * |x|) using le_abs_self and abs_mul. Then ‖z‖ * exp(a|x|) ≤ P * exp(-δx²) * exp(a|x|) = P * exp(-δx²+a|x|) by Real.exp_add, and exp_neg_mul_sq_add_mul_le finishes with mul_le_mul_of_nonneg_left.

First derivative: unfold poitouVerticalProfileDerivative, then factor the sum as ((kd:ℂ) + (σ-1/2) * (k:ℂ)) * exp(...) by ring. Take z = kd + (σ-1/2) k, P = C + 2δ|x| + 1/2 + a, and get ‖z‖ ≤ |kd| + a|k| from norm_add_le and Complex.norm_real, using hkd and hk.

Second derivative: factor as (k'' + 2(σ-1/2)kd + (σ-1/2)² k) * exp(...), take P as the existing polynomial, and bound ‖z‖ by |k''| + 2a|kd| + a²|k| from the same hk, hk', hk'' hypotheses.

This deletes the duplicated hphase, simp/hnorm and exp-merge blocks from both proofs, and the second proof loses its repeated hP/hP₂ nonnegativity argument.

Benefit: The decay argument (phase growth against Gaussian decay) is stated and proved once. Each theorem then only checks its own polynomial prefactor, so the long calc chains with repeated polynomial expressions shrink a lot. A change to the Gaussian/phase argument is made in one place.

Source evidence:

- `norm_poitouVerticalProfileSecondDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:         _ ≤ _ := mul_le_mul_of_nonneg_left
          (exp_neg_mul_sq_add_mul_le hδ a x) hP
- `exp_neg_mul_sq_add_mul_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean`: Real.exp (-δ * x ^ 2 + a * |x|) ≤
      Real.exp (a ^ 2 / (2 * δ)) *

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L127)

Declaration: `exists_positive_shell`

The proof locates a dyadic index with `k = ⌊log x / log 2⌋`. It proves `2^k ≤ x < 2^(k+1)` through the two log/rpow monotonicity calculations `hpowlo` and `hpowhi`, then multiplies back by `R`. `exists_shell_of_pos_lt` in Kernel.lean (lines 178–215), which Tail already imports, repeats this reasoning almost line for line. The setup `x`, `L`, `k`, `hL`, `hklo`, `hkhi` is the same, and so are `hpowlo`, `hpowhi`, `hinner`, `houter`. Only the sign argument for `k` differs (`0 ≤ k` here, `k < 0` there). The two copies are about 30 lines each and must be maintained in parallel.

Proposed change:

Add one lemma in Kernel.lean before `exists_shell_of_pos_lt`, for example `exists_int_shell {z w} {R} (hR : 0 < R) (hρ : 0 < parabolicRho₂ z w) : ∃ k : ℤ, w ∈ parabolicRieszShell R k z`. Its proof is the shared floor-log argument (`hpowlo`, `hpowhi`, `hinner`, `houter`, `mem_parabolicRieszShell`). Alternatively, use Mathlib's `Int.log` and `zpow_log_le_self`/`lt_zpow_succ_log_self`, after converting the rpow with an integer exponent to `zpow`. Then add a sign lemma: `w ∈ parabolicRieszShell R k z → parabolicRho₂ z w < R → k < 0`, using `2^k * R ≤ ρ < R`. Add a second sign lemma: `w ∈ parabolicRieszShell R k z → R ≤ parabolicRho₂ z w → 0 ≤ k`, using `R ≤ ρ < 2^(k+1) R`. Both come from strict monotonicity of `2 ^ ·`. Then `exists_shell_of_pos_lt` becomes `obtain ⟨k, hmem⟩ := exists_int_shell hR hρ; exact ⟨k, neg_lemma hmem hρR, hmem⟩`. `exists_positive_shell` becomes `obtain ⟨k, hmem⟩ := exists_int_shell hR (hR.trans_le hRρ); exact ⟨k.toNat, by simpa [Int.toNat_of_nonneg (nonneg_lemma hmem hRρ)] using hmem⟩`. Here `hR.trans_le hRρ : 0 < parabolicRho₂ z w`, which supplies the positivity the shared lemma needs. The degenerate case `ρ = 0` is excluded in both uses. Positive shells have `ρ ≥ R > 0`, and negative shells assume `0 < ρ`.

Benefit: The floor/log/rpow argument exists in one place. Both existence lemmas shrink to a short sign argument. Any change to the shell definition, such as a different base, is then made once.

Source evidence:

- `exists_shell_of_pos_lt` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:   have hpowlo : (2 : ℝ) ^ (k : ℝ) ≤ x := by
    apply (Real.strictMonoOn_log.le_iff_le
- `parabolicRieszShell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:   {w | (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w ∧

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L161)

Declaration: `positiveShell_pairwise`

Pairwise disjointness of dyadic shells is proved here for ℕ indices. Kernel.lean's private `pairwise_disjoint_parabolicRieszShells` proves it for negative ℤ indices, again with two symmetric branches. Each branch derives `2^(a+1) ≤ 2^b` from `a < b`, multiplies by `R`, and contradicts `hw.2 : ρ < 2^(a+1) R` with `hw.1 : 2^b R ≤ ρ`. The nontrivial step is that shells with distinct integer indices are disjoint. It is proved twice, and the ℕ copy has extra casts through ℤ and ℝ.

Proposed change:

Prove once in Kernel.lean a public lemma `parabolicRieszShell_disjoint {R} (hR : 0 < R) {k l : ℤ} (hkl : k < l) (z) : Disjoint (parabolicRieszShell R k z) (parabolicRieszShell R l z)`. The proof is the first branch, using `Int.add_one_le_iff.mpr hkl`. Then use `Disjoint.symm` for the other order. Both pairwise statements reduce to it. `pairwise_disjoint_parabolicRieszShells` becomes `intro k l hkl; rcases lt_or_gt_of_ne hkl with h | h; exacts [disj hR h z, (disj hR h z).symm]`, with `h` first converted by `Subtype.coe_lt_coe`. `positiveShell_pairwise` becomes the same with `Nat.cast_lt` and `Nat.cast_injective`. Exact coercion lemma names are not checked. There are no new hypotheses: `0 < R` is already in both statements.

Benefit: The two copies, with different cast plumbing, reduce to a single disjointness fact. This is clearer because the Tail file then only handles the ℕ→ℤ index cast.

Source evidence:

- `pairwise_disjoint_parabolicRieszShells` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hpow hR.le).trans
      hwl.1)) hwk.2

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L206-L263)

Declaration: `weakPathRepresentative_pairing_eq_inner and FrozenDriftProblem.initial_pairing_eq_cell_integral`

The two proofs repeat the same argument. A torus L² inner product is rewritten via `L2.inner_def` and `mul_comm` as `∫ x : Torus, f x * ψT x`. The a.e. identifications of `f` and of `ψT` with `periodicToTorus` are then used to rewrite the integrand as `periodicToTorus (fun y => g y * ψ y)`. After that the chain applies `integral_periodicToTorus_eq_unitCell` and then `integral_unitCell_eq_unitCube`. The `htest` and `hψT` blocks, which obtain the a.e. identification of `smoothPeriodicTestL2` via `coeFn_toLp`, are also identical. The two proofs run the chain in opposite directions, so the shared structure is not obvious. Any change to the test-function class, such as new hypotheses on `smoothPeriodicTestL2`, must be made in both places.

Proposed change:

Add one lemma before `weakPathRepresentative_pairing_eq_inner`:

theorem torus_inner_smoothPeriodicTestL2_eq_cell_integral (f : ScalarTorusL2) {g ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) (hfg : (fun x : Torus => f x) =ᵐ[volume] AVenhance.Infra.Torus.periodicToTorus g) : inner ℝ f (smoothPeriodicTestL2 hψ hperiodic) = ∫ x in AVenhance.unitCube, g x * ψ x.

Proof: this is the body of `initial_pairing_eq_cell_integral`, with `P.initialTorusL2` replaced by `f`, `P.θ₀` by `g`, and `hθ` by `hfg`. That is, `let ψT := smoothPeriodicTestL2 hψ hperiodic`; obtain `hψT` from `coeFn_toLp`; then run the same `calc`: `L2.inner_def`, `mul_comm`, `integral_congr_ae` with `filter_upwards [hfg, hψT]`, `integral_periodicToTorus_eq_unitCell`, `integral_unitCell_eq_unitCube`.

Rewritten uses:
- `FrozenDriftProblem.initial_pairing_eq_cell_integral`: `exact torus_inner_smoothPeriodicTestL2_eq_cell_integral P.initialTorusL2 hψ hperiodic (frozenInitialData_memLp_torus P.initial_memL2).coeFn_toLp`.
- `weakPathRepresentative_pairing_eq_inner`: keep `htheta` (which is `periodicToTorus (weakPathRepresentative u t) x = u t x`), then `exact (torus_inner_smoothPeriodicTestL2_eq_cell_integral (u t) hψ hperiodic (Filter.Eventually.of_forall fun x => (htheta x).symm)).symm`.

Both uses keep their actual hypotheses (`hψ`, `hperiodic`, `P.initial_memL2`, `t.property`) and need no new imports.

Benefit: The Fubini-style torus/cell bookkeeping and the product-of-`periodicToTorus` rewrite live in one place. Each of the two theorems shrinks to the part specific to it: the a.e. identification of the datum, or the pointwise identity `htheta`. The direction mismatch between the two calc chains disappears. Future changes to the pairing, such as a different test class or measure normalization, are made once.

Source evidence:

- `AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: ∫ x : UnitAddTorus (Fin d), periodicToTorus f x = ∫ x in unitCell d, f x
- `AVenhance.Infra.Torus.integral_unitCell_eq_unitCube` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: ∫ x in unitCell 2, f x = ∫ x in AVenhance.unitCube, f x
- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: _ = ∫ x : Torus, inner ℝ (u t x) (ψT x) := by
