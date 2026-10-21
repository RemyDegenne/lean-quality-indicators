# Findings

### missing-structure: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L46-L51)

Declaration: `Algebra.TensorProduct.basisAux (with basisAux_map_smul and basis)`

The docstring says the equivalence is "in fact A-linear", but it is bundled only as an R-linear equiv. A-linearity is a separate theorem, `basisAux_map_smul`, proved by tensor induction. `basis` then has to rebuild the repr with `{ basisAux A b with map_smul' := basisAux_map_smul b }`. Mathlib already has A-linear (heterobasic) equivalences that give exactly this map: `TensorProduct.AlgebraTensorModule.congr` is A-linear, and `TensorProduct.finsuppScalarRight R S M ι : M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M` is stated for S-linearity. Taking S = A and M = A, the composite `AlgebraTensorModule.congr (.refl A A) b.repr ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι` is an `A`-linear equiv `A ⊗[R] M ≃ₗ[A] ι →₀ A`. It applies under the file's assumptions, because `finsuppScalarRight` needs only `Semiring S` and `Algebra R S`. The hand-rolled `TensorProduct.congr`, `finsuppTensorFinsupp`, `Finsupp.lcongr` and `Equiv.uniqueProd` pipeline and the extra smul lemma are therefore avoidable.

Proposed change:

Make `basisAux` an A-linear equivalence: `basisAux : A ⊗[R] M ≃ₗ[A] ι →₀ A := AlgebraTensorModule.congr (.refl A A) b.repr ≪≫ₗ TensorProduct.finsuppScalarRight R A A ι`, using `open scoped Classical` or a `DecidableEq ι` argument as `finsuppRight` requires. Then define `basis A b := Basis.ofRepr (basisAux A b)` and delete `basisAux_map_smul`. Re-derive `basisAux_tmul` and `basis_repr_symm_apply` from `finsuppScalarRight_apply_tmul_apply` and `finsuppScalarRight_symm_apply_single`.

Benefit: The A-linear structure is exposed in the type of the auxiliary object instead of in a side lemma, so users get `map_smul`, `trans` and `symm` for the A-structure directly. `basis` becomes a one-line `Basis.ofRepr`, and the manual tensor-induction proof of `basisAux_map_smul` disappears. The file also reuses the standard `finsuppScalarRight` API, the same equivalence that `IsBaseChange.of_basis` already uses.

Source evidence:

- `Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: repr := { basisAux A b with map_smul' := basisAux_map_smul b }
- `TensorProduct.finsuppScalarRight` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/DirectSum/Finsupp.lean`: M ⊗[R] (ι →₀ R) ≃ₗ[S] ι →₀ M
- `TensorProduct.AlgebraTensorModule.congr` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Tower.lean`: def congr (f : M ≃ₗ[A] P) (g : N ≃ₗ[R] Q) : (M ⊗[R] N) ≃ₗ[A] (P ⊗[R] Q)
- `IsBaseChange.of_basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/IsBaseChangeFree.lean`: let j := TensorProduct.finsuppScalarRight A R R ι

### missing-structure: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L150-L154)

Declaration: `bijective_rootsOfUnityAddChar`

ZMod.rootsOfUnityAddChar is a bundled AddChar from ZMod n to rootsOfUnity n Circle. The file proves it is bijective, which makes it an isomorphism ZMod n ≃ μ_n. The isomorphism is exposed only as a Bijective fact about the underlying function. The same file works with the surjectivity half through the unbundled composite `rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n`. Anyone who wants an equivalence, such as an inverse, a symm, or transport of structure, has to rebuild it from `Bijective` themselves.

Proposed change:

Bundle the bijection as a group isomorphism, for example `ZMod.rootsOfUnityAddEquiv n : Multiplicative (ZMod n) ≃* rootsOfUnity n Circle`, or the additive version into `Additive (rootsOfUnity n Circle)`. Build it from the existing AddChar's monoid hom and the proved bijectivity, using the standard `ofBijective` constructor. Keep `bijective_rootsOfUnityAddChar` as a corollary or as the construction input. Then state the composite with `rootsOfUnityCircleEquiv` as an equivalence composition (a `trans` of two equivalences) instead of `∘` on functions.

Benefit: Users get an inverse and a `symm` that identify the roots of unity in the circle with ZMod n. The composite with rootsOfUnityCircleEquiv becomes a composition of MulEquivs, so the bijectivity argument no longer needs the `Surjective.of_comp_left` plus injectivity juggling. The cost is one definition and its coercion lemma.

Source evidence:

- `surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: Surjective (rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n)
- `ZMod.rootsOfUnityAddChar` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: AddChar (ZMod n) (rootsOfUnity n Circle) where
- `rootsOfUnityCircleEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: noncomputable def rootsOfUnityCircleEquiv : rootsOfUnity n Circle ≃* rootsOfUnity n ℂ where

### missing-structure: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L516-L557)

Declaration: `LinearMap.taylorComponent (with taylorComponent_zero, taylorComponent_add, taylorComponent_smul)`

For fixed n, `b ↦ taylorComponent b n` is R-linear in the endomorphism b. It is defined as the composite of `letter` after b, then precomposition with `of R M n`. That linearity is exposed only as three separate lemmas (zero/add/smul) about a bare function, not as a linear map. So `map_zero`, `map_add`, `map_smul`, `map_sum` and `LinearMap.ker` cannot be used on it. The linearity is also not shown to be the one that makes `coderivEquivTaylor`'s `toFun` (`letter ∘ₗ b.1`) linear.

Proposed change:

Add a bundled linear map such as `taylorComponentₗ (n) : (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) →ₗ[R] (TensorPower R n.1 M →ₗ[R] M)`. Its `toFun` is the existing `taylorComponent · n`, and `map_add'`/`map_smul'` are the existing `taylorComponent_add`/`taylorComponent_smul` proofs. It could also be written as a composite of the standard `LinearMap.compRight`/`LinearMap.lcomp` bundles. Keep `taylorComponent` as the named operation with a `@[simp]` coe lemma. Then `taylorComponent_zero/add/smul` follow from `map_zero`/`map_add`/`map_smul`.

Benefit: Consumers can use generic `map_*`/`map_sum` and kernel reasoning for the Taylor-component map. The statement that a coderivation vanishes iff all its arity components vanish becomes a statement about the kernels of these linear maps. The bundling costs only a few lines, since the proofs already exist.

Source evidence:

- `AInfinity (square-zero criterion proof)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Homology/AInfinity/Coderivation.lean`: simp only [LinearMap.taylorComponent_zero, LinearMap.zero_apply] at hcomponent
- `coderivEquivTaylor` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean`: toFun b := letter R M ∘ₗ b.1

### missing-structure: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L324-L331)

Declaration: `TauCeti.exists_normalDisc`

The docstring describes `ψ z : ℂ → ℝ³` as a family of linear isometries onto the normal planes. The statement exposes it as a bare function with separate facts: norm preservation, injectivity, and landing in and surjecting onto the normal subspace. Linearity is not stated at all. Injectivity is a consequence of being a linear isometry, but it is carried as an extra conjunct, and the proof re-derives it by hand from the `h₁`/`h₂` coordinate computations. The consumer then unfolds the norm and injectivity facts manually.

Proposed change:

State the result with `ψ : Circle → ℂ →ₗᵢ[ℝ] ℝ³`, keeping continuity of `fun q : SolidTorus => ψ q.2 q.1` and the range facts (`∀ w, ψ z w ∈ normalSubspace ..` and surjectivity onto it). Build `ψ z` from `fun w => w.re • n₁ z + w.im • n₂ z`. Linearity is a short computation, and `norm_map'` is the existing norm computation. Drop the explicit `Injective (ψ z)` conjunct and obtain injectivity from `(ψ z).injective`, and the norm fact from `(ψ z).norm_map`. The `r • ψ q.2 q.1` in `exists_isSolidTorusNeighborhood` would then use `LinearIsometry.norm_map` and `LinearIsometry.injective`.

Benefit: The statement matches its docstring and carries the linear isometry structure as one object. It removes redundant hypotheses and gives the consumer the standard `LinearIsometry` API (`norm_map`, `injective`, `range`) instead of hand-written conjuncts.

Source evidence:

- `LinearIsometry` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`: structure LinearIsometry (σ₁₂ : R →+* R₂) (E E₂ : Type*) [SeminormedAddCommGroup E]
- `TauCeti.exists_isSolidTorusNeighborhood` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: rw [norm_smul, (hψ q.2).2.1, Real.norm_of_nonneg hr.le]

### missing-structure: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L152-L178)

Declaration: `clm_indicator'_eq_additiveFunction / zero_mem_convexHull_of_best_approx (use of additiveFunction a S under negation and scaling by ε)`

`additiveFunction a S = ∑ i ∈ S, a i` is linear in the weight vector `a`. It is also additive over disjoint sets and vanishes at ∅, which is the "additive signed measure" structure from Defs. None of this is exposed as a bundled object, so every proof unfolds the sum and redoes the algebra. In this file the proof unfolds `additiveFunction` to see that negating `a` negates the value (lines 162–164). It also unfolds it to see that `additiveFunction (fun i => ε' * a i) S` scales by `ε'` (the `simp only [additiveFunction]` at line 176 and the `← Finset.mul_sum` rewrites in `h_active`). The same unfolding appears in Pipeline.lean for `distToAdditive_sub_additive` and `distToAdditive_neg`, with `Finset.sum_sub_distrib`, `Finset.sum_add_distrib` and `Finset.sum_neg_distrib`. The `fun i => ε * a i` and `fun i => -a i` arguments are also scalar multiples and negations of `a`, but they appear only as opaque lambdas.

Proposed change:

Expose the linearity in `a` as a bundled map `(U → ℝ) →ₗ[ℝ] (Finset U → ℝ)`, or equivalently a family `S ↦ ∑ i ∈ S, LinearMap.proj i : (U → ℝ) →ₗ[ℝ] ℝ`. Its fields follow from `Finset.sum_add_distrib` for `map_add'` and `Finset.mul_sum` for `map_smul'`. Keep `additiveFunction a S` as the named operation, with a simp lemma stating that it equals the bundled map applied to `a`. State the weight scalings as `ε • a` and `-a`, so the algebra in the ε-perturbation step and in Pipeline.lean's `distToAdditive_neg` and `distToAdditive_sub_additive` becomes `map_smul`, `map_neg` and `map_sub`. In `h_additiveFunction_a_neg`, it would be `map_neg` plus the `clm_indicator'` lemma. The ε-perturbation could then be written as `|f S - ε * additiveFunction a S|`, which is continuous in `ε` by `fun_prop`, so the `continuity` call at line 177 is not needed.

Benefit: The sum-unfolding proofs in this file and in Pipeline.lean's `distToAdditive_neg` and `distToAdditive_sub_additive` shrink to `map_*` rewrites. The structure the docstring in Defs describes (additive measures identified with weight functions) becomes visible in the API. The cost is one small definition and one coercion lemma.

Source evidence:

- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i
- `distToAdditive_neg` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Pipeline.lean`: simp only [additiveFunction, Finset.sum_neg_distrib]
- `distToAdditive_sub_additive` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Pipeline.lean`: simp +decide [ additiveFunction, Finset.sum_sub_distrib ]
- `LinearMap.proj` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/LinearAlgebra/Pi.lean`: def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where

### missing-structure: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L70-L75)

Declaration: `clm_indicator'_eq_additiveFunction`

The correspondence between a functional `Λ : (U → ℝ) →L[ℝ] ℝ` and its weight vector `fun i => Λ (Function.update 0 i 1)` is an anonymous lambda, repeated at lines 72, 152 and 155. The lemma is stated pointwise as a `Λ`-versus-`additiveFunction` identity. The weight map `Λ ↦ (i ↦ Λ (Pi.single i 1))` is itself linear, and `S.indicator'` is the sum of the basis vectors over `S`. This structure appears only as one-off lemmas, so the later negation step has to be rebuilt by unfolding `additiveFunction`.

Proposed change:

Name the weight vector once, as a definition (for example `weights Λ : U → ℝ := fun i => Λ (Pi.single i 1)`). If the linearity-in-`a` bundle from the first finding exists, restate the lemma as `Λ S.indicator' = additiveFunction (weights Λ) S`, with `weights` a linear map or function in `Λ`. Then `weights (-Λ) = -weights Λ` and `weights` applied to `Λ` give the sign flip at lines 152–165 directly. This is optional and depends on the first finding.

Benefit: One named object replaces the inline lambda and its repeated `convert` and `simp_all` rewriting at lines 155–157. The sign and negation facts can then be stated once, with `Λ` and `-Λ` handled by `map_neg`.

Source evidence:

- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: set a : U → ℝ := fun i => -(Λ (Function.update 0 i 1)) with ha_def;
- `LinearMap.pi_apply_eq_sum_univ` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/LinearAlgebra/Pi.lean`: f x = ∑ i, x i • f fun j => if i = j then 1 else 0

### missing-structure: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L64-L70)

Declaration: `sectorCurve (with sectorCurve_continuousOn, sectorCurve_closed, deriv_sectorCurve_seg1/2/3)`

`sectorCurve` is a closed piecewise-C¹ curve on [0,3] with knots {0,1,2,3}. The file proves its structure only as unbundled facts: `sectorCurve_continuousOn`, `sectorCurve_closed`, and the per-segment `deriv_sectorCurve_seg1/2/3`. The off-knot differentiability is a private lemma in another file (`sectorCurve_differentiableAt_off_knots`). The library already has the standard bundle `PiecewiseC1Curve`, with fields `continuous_toFun`, `smooth_off_partition` and `deriv_continuous_off_partition`, an `IsClosed` predicate, and a `Bridges.lean` API (`toPath`, `toLoop`). These fields all follow from lemmas that already exist. The sector curve therefore cannot be passed to any of that machinery, such as `PiecewiseC1Curve.toLoop`, `toPath`, or the curve-taking theory, without redoing the work.

Proposed change:

Add `def sectorC1Curve (r α : ℝ) : PiecewiseC1Curve` with `toFun := sectorCurve r α`, `a := 0`, `b := 3`, `hab := by norm_num`, and `partition := {0,1,2,3}`. Take `continuous_toFun := sectorCurve_continuousOn r α`. For `smooth_off_partition`, promote `sectorCurve_differentiableAt_off_knots` (currently private in SectorCurveLemma) and move it into this file. For `deriv_continuous_off_partition`, use `deriv_sectorCurve_seg1/2/3` together with the open-neighbourhood eventual equalities. Add the lemma `(sectorC1Curve r α).IsClosed` from `sectorCurve_closed`. Keep `sectorCurve` and the named lemmas as the computational API, and state `sectorCurve_continuousOn` as a corollary of the bundle's field. Optionally add a `PiecewiseC1Immersion` version for `r ≠ 0` and `α ≠ 0`.

Benefit: Users can apply the generic curve API directly. For example, `PiecewiseC1Curve.toLoop` gives the sector curve as a Mathlib `Path`/loop. Hypotheses of the form `(γ : PiecewiseC1Curve)` and `γ.IsClosed` can be discharged by one term rather than re-proved per curve. The scattered differentiability, continuity and closedness facts get one authoritative statement, and the private off-knot differentiability lemma stops being a hidden duplicate of a field.

Source evidence:

- `PiecewiseC1Curve` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean`: smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t
- `PiecewiseC1Curve.IsClosed` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean`: γ.toFun γ.a = γ.toFun γ.b
- `PiecewiseC1Curve.toLoop` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Bridges.lean`: def toLoop (γ : PiecewiseC1Curve) (hc : γ.IsClosed) :
- `sectorCurve_differentiableAt_off_knots` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: DifferentiableAt ℝ (sectorCurve r α) t := by

### missing-structure: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L187-L191)

Declaration: `planeCurveFrobeniusRelation`

The definition is a bare function `f ↦ planeCurveToBivariate F (MvPolynomial.map ι f)`. It is a composite of a ring hom `MvPolynomial.map ι` and an `AlgEquiv`, so it is a ring homomorphism, and an injective one. The file exposes that only through separate unbundled facts: `_natDegree`, `transposeBivariate_..._natDegree`, `_irreducible` and `evalBivariate_...`. The proof of `evalBivariate_planeCurveFrobeniusRelation` rebuilds the bundled map by hand as `(planeCurveToBivariate F).toRingEquiv.toRingHom.comp (MvPolynomial.map ι)`. `planeCurveFrobeniusRelation_irreducible` re-derives preservation of irreducibility by `.map` on a `MulEquiv`. Both degree lemmas unfold the definition with `rw [planeCurveFrobeniusRelation, ...]`.

Proposed change:

Define a bundled map first. For example, `planeCurveFrobeniusRelationHom : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial (frobeniusSubfield L p))`, defined as `(planeCurveToBivariate F).toRingEquiv.toRingHom.comp (MvPolynomial.map ι)`. Then set `planeCurveFrobeniusRelation f := planeCurveFrobeniusRelationHom f`, or use the hom directly. State the C/X generator values once and use `MvPolynomial.ringHom_ext`. The hand-built `lhs` in `evalBivariate_planeCurveFrobeniusRelation` is then just `evalIterated.comp planeCurveFrobeniusRelationHom`. Injectivity of the hom (composition of `MvPolynomial.map_injective` with an equiv) gives a uniform `map_...` / `Irreducible.map`-style route for irreducibility.

Benefit: The ring-hom structure becomes one public object that the evaluation, irreducibility and degree lemmas share. The proof of `evalBivariate_planeCurveFrobeniusRelation` no longer has to rebuild the composite inline. Later users get `map_mul`, `map_add` and `ringHom_ext` for free.

Source evidence:

- `evalBivariate_planeCurveFrobeniusRelation` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: let lhs : MvPolynomial (Fin 2) K →+* L :=
    evalIterated.comp
      ((planeCurveToBivariate F).toRingEquiv.toRingHom.comp
        (MvPolynomial.map ι))
- `planeCurveFrobeniusRelation_irreducible` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: exact hbaseChange.map
    (planeCurveToBivariate (frobeniusSubfield L p)).toMulEquiv

### missing-structure: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L227-L233)

Declaration: `evalBivariate_planeCurveFrobeniusRelation (use of unbundled evalBivariate)`

`evalBivariate u v` (upstream, in AuxiliaryFamily.lean) is a plain function `P.eval₂ (eval₂RingHom (algebraMap C L) u) v`. It is a ring hom `C[U][V] →+* L`, but that is not exposed. Its additivity and multiplicativity exist only as `private` lemmas `evalBivariate_add` and `evalBivariate_mul` in BivariateResultant.lean. Each consumer therefore rebuilds the ring hom by hand: this file at lines 227–229, PlaneConstantField.lean `evalBivariate_planeCurveToBivariate`, and BivariateResultant `eval₂_resultant_eq_zero_of_common_zero`. The `evalBivariate_transposeBivariate` proof needs a manual `induction P using Polynomial.induction_on'`. The proof of `evalBivariate_planeCurveFrobeniusRelation` also repeats the generator-by-generator check already done for `planeCurveToBivariate` in PlaneConstantField.

Proposed change:

Add a public bundled `evalBivariateHom (u v : L) : Polynomial (Polynomial C) →+* L` (or an `AlgHom` over `C`), defined as `Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap C L) u) v`. Redefine or characterize `evalBivariate u v` as its coercion, drop the private add/mul lemmas, and use it in this file. Then `evalBivariate_planeCurveFrobeniusRelation` becomes: evaluate `planeCurveToBivariate F (map ι f)` through the existing generic lemma `evalBivariate_planeCurveToBivariate` (with `F` as base and the scalar-tower `algebraMap F L`), followed by `MvPolynomial.eval₂_map` and the equality `algebraMap F L ∘ ι = algebraMap K L`. The generator-by-generator `ringHom_ext` argument then disappears from this file.

Benefit: One bundled evaluation hom replaces four hand-built copies and the private add/mul lemmas. It gives `map_*` lemmas for free and shortens the Frobenius evaluation lemma to a base-change composition.

Source evidence:

- `evalBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/AuxiliaryFamily.lean`: def evalBivariate (u v : L) (P : Polynomial (Polynomial C)) : L :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap C L) u) v
- `evalBivariate_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/BivariateResultant.lean`: private theorem evalBivariate_mul
- `evalBivariate_planeCurveToBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/HasseWeil/PlaneConstantField.lean`: (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap K L) y) x).comp

### repeated-proof-machinery: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L86-L90)

Declaration: `Profinite.effectiveEpiFamily_tfae`

The argument that transfers the jointly-surjective / effective-epi-family equivalence from CompHaus along a fully faithful forgetful functor is repeated verbatim in Stonean.effectiveEpiFamily_tfae, with only the functor changed. The common steps are: (1) 2 → 1 via effectiveEpi_desc_iff_effectiveEpiFamily and effectiveEpi_tfae; (2) 1 → 2 by an instance; (3) 3 ↔ 1 by rewriting with CompHaus.effectiveEpiFamily_tfae applied to the image family and then using finite_effectiveEpiFamily_of_map. The effectiveEpi_tfae proof and the PreservesEffectiveEpis/ReflectsEffectiveEpis instances are likewise duplicated across Profinite, Stonean and CompHaus. Any fix to the fragile erw step has to be made in each copy.

Proposed change:

Add one helper that takes a functor F : C ⥤ CompHaus, with the existing hypotheses used here (F preserves finite coproducts, F.ReflectsEffectiveEpis or the hypothesis finite_effectiveEpiFamily_of_map needs, and F preserves the underlying-set action). It would state that, for a finite family π into B, EffectiveEpiFamily X π is equivalent to joint surjectivity. Profinite.effectiveEpiFamily_tfae and Stonean.effectiveEpiFamily_tfae would then call it with profiniteToCompHaus and Stonean.toCompHaus. This is not tested, and the instance hypotheses would need to be checked.

Benefit: The transfer argument and its erw workaround live in one place. Each category file shrinks to a one-line application, and a future generalization (for example the `Type*` TODO) needs only one change.

Source evidence:

- `Stonean.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Stonean/EffectiveEpi.lean`: erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a ↦ Stonean.toCompHaus.obj (X a)) (fun a ↦ Stonean.toCompHaus.map (π a))).out 3 1 :)]
    exact ⟨fun h ↦ Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
- `CompHaus.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/CompHaus/EffectiveEpi.lean`: simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 1 2]

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293)

Declaration: `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

The two theorems have the same proof. Both take (hf.mul hg).trans (Eventually.isBigO ?_), then restrict to t ≥ 1, combine t^a * t^b into t^(a+b) with rpow_add, drop the norm with norm_of_nonneg, and finish with rpow_le_rpow_of_exponent_le. The ℕ version differs only by a Nat.one_le_cast step. So the analytic core, ‖t^a * t^b‖ ≤ ‖t^c‖ for t ≥ 1 and a+b ≤ c, is written out twice.

Proposed change:

Add one real-variable helper, e.g. `lemma isBigO_rpow_add_atTop_of_le (h : a + b ≤ c) : (fun t : ℝ => t ^ a * t ^ b) =O[atTop] fun t : ℝ => t ^ c`, with the filter_upwards/rpow_add/rpow_le_rpow_of_exponent_le proof once. Then the ℝ lemma is `(hf.mul hg).trans (helper h)`. The ℕ lemma is `(hf.mul hg).trans ((helper h).comp_tendsto tendsto_natCast_atTop_atTop)`. The ℕ call then needs no `1 ≤ (t:ℝ)` cast step, and the hypotheses are unchanged (a, b, c real, a + b ≤ c, E a SeminormedRing).

Benefit: The inequality argument is proved once, so the two public lemmas shrink to one-line wrappers. The ℕ version is then visibly just the ℝ version composed with the cast. Future changes to the exponent bound only need to be made in one place.

Source evidence:

- `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: refine (hf.mul hg).trans (Eventually.isBigO ?_)
- `Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
- `call sites of both lemmas` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`: IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L324)

Declaration: `Bundle.Trivialization.mk_coordChangeL and VectorPrebundle.mk_coordChange`

`mk_coordChangeL` (about line 316) and `VectorPrebundle.mk_coordChange` (about line 858) have the same proof of `(b, _) = e' ⟨b, e.symm b y⟩`. Both do `ext`. For the first component, both run the rewrite chain `e.mk_symm hb.1 _`, `e'.coe_fst'`, `e.proj_symm_apply' hb.1`, then a second `proj_symm_apply'` and `exact hb.2`. This is the fact that `e'` applied to `⟨b, e.symm b y⟩` has first component `b` when `b` lies in both base sets. Only the second component, which is the `coordChangeL_apply` / `coordChange_apply` fact, differs. The statement for `Trivialization.mk_coordChange` already exists in `Mathlib/Topology/FiberBundle/Trivialization.lean` and covers the same situation as `mk_coordChangeL`. Its RHS uses `e₁.toOpenPartialHomeomorph.symm (b, x)`, which `mk_symm` converts to `e.symm b y`. The file itself has `coordChangeL_apply'`, which shows `coordChangeL` agrees with that unfolded form.

Proposed change:

1. Prove `mk_coordChangeL` by reusing the existing `Bundle.Trivialization.mk_coordChange` from FiberBundle/Trivialization.lean. Rewrite with `coordChangeL_apply'` and `e.mk_symm hb.1`, then close with `e.mk_coordChange e' hb.1 hb.2 y`. This removes the `ext` and the rewrite chain at lines 319–324.
2. For `VectorPrebundle.mk_coordChange`, extract one small Pretrivialization-level lemma: for `hb : b ∈ e.baseSet ∩ e'.baseSet`, `(e' ⟨b, e.symm b y⟩).1 = b`. Place it next to `Pretrivialization.mk_symm` or in this file's Pretrivialization namespace.
3. Reduce `VectorPrebundle.mk_coordChange` to `Prod.ext (that lemma).symm (a.coordChange_apply he he' hb v)`.

This lemma should also be usable from the Trivialization side.

Benefit: The "first component is b" argument is proved once instead of twice, so the two coordinate-change lemmas shrink to their genuine second-component content. The Trivialization case reuses a lemma that already exists in the library. The repeated `proj_symm_apply'` step with its awkward double `rw` disappears from both places.

Source evidence:

- `VectorPrebundle.mk_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:   · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
- `Bundle.Trivialization.mk_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean`: (b, e₁.coordChange e₂ b x) = e₂ (e₁.toOpenPartialHomeomorph.symm (b, x))
- `Bundle.Trivialization.coordChangeL_apply'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: coordChangeL R e e' b y = (e' (e.toOpenPartialHomeomorph.symm (b, y))).2

### repeated-proof-machinery: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L433-L451)

Declaration: `TauCeti.ReducedTensorWords.letter_comp_coderiv`

The proof of `letter_comp_coderiv` is a double `Finset.sum_eq_single` argument. It picks out the `(p, d) = (0, n)` summand of the expansion with `letter_splice_eq_zero_of_not_whole` and `letter_splice_self`, and discards the remaining summands. `letter_comp_gradedCoderiv` in GradedCoderivation.lean repeats the same steps line for line. It differs only in that the tuple is `twistedTuple G q x 0 p` instead of `x`. The two proofs share the bookkeeping: the two `sum_eq_single` calls, the `absurd` side goals on `Finset.mem_range`, and the omega side conditions. Any change to the splice or letter API has to be made twice.

Proposed change:

Add a helper next to `letter_splice_self`, stated for an arbitrary family of tuples and coefficients:
`theorem letter_sum_splice_eq {n : ℕ} (hn : 0 < n) (y : ℕ → Fin n → M) (e : ℕ → ℕ → M) : letter R M (∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n + 1), splice R (y p) 0 n p d (e p d)) = e 0 n`.
The proof is the current `sum_eq_single` argument, using `map_sum`, `letter_splice_eq_zero_of_not_whole` and `letter_splice_self`. Then `letter_comp_coderiv` becomes `rw [..coderiv_subword..]; exact letter_sum_splice_eq R hn (fun _ ↦ x) (fun p d ↦ F (subword R x p d))`. The graded version uses `y p = twistedTuple G q x 0 p` and the same `e`. The graded case needs `y 0` rather than a fixed `x`. The family `y` covers this, because `letter_splice_self` is applied at `p = 0`, where the twist is empty.

Benefit: The "only the whole-word collapse survives the letter projection" argument is proved once, with its hypotheses stated explicitly. Both `letter_comp_coderiv` and `letter_comp_gradedCoderiv` reduce to a short rewrite. A reader sees that the graded case differs only in the tuple, not in the combinatorics.

Source evidence:

- `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`:   refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro p _ hp
    refine Finset.sum_eq_zero fun d _ ↦
      letter_splice_eq_zero_of_not_whole R (twistedTuple G q x 0 p) _ (by omega)
- `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`:     · exact letter_splice_self R (twistedTuple G q x 0 0)
        (F (subword R x 0 n)) hn (by omega)

### repeated-proof-machinery: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L225-L233)

Declaration: `TauCeti.schwarzChristoffelBoundary_injOn (also collinear_schwarzChristoffelBoundary_image, schwarzChristoffelBoundary_sub_eq, continuousOn_schwarzChristoffelBoundary)`

Four theorems on a prevertex-free interval share one bridge. Each obtains an auxiliary L from an Edge lemma (`exists_tendsto_schwarzChristoffelPrimitive_sub_eq` or `..._injOn_collinear`). Each then converts L's pointwise limit property into an equality `schwarzChristoffelBoundary a e z₀ x = L x` via `schwarzChristoffelBoundary_eq_of_tendsto`, re-doing the conversion at x and y or via a hand-written `ext`/`rintro` set-image argument. The Edge lemmas bundle the facts about L with an unconstrained L, so every consumer has to transfer them to the boundary map by hand. `collinear_schwarzChristoffelBoundary_image` spends about ten lines on this, using `convert` and a two-direction `ext`. The same `obtain` plus limit-to-equality step also appears in Infinity/Basic.lean, with `limUnder_eq`.

Proposed change:

Add one private (or public) lemma stating that on `Ioo p q` the boundary map has the same limit data as the Edge lemmas. A simple form is `∀ x ∈ Ioo p q, Tendsto (schwarzChristoffelPrimitive a e z₀) (𝓝[upperHalfPlaneSet] (x:ℂ)) (𝓝 (schwarzChristoffelBoundary a e z₀ x))`. This follows from `tendsto_schwarzChristoffelPrimitive_boundary` with the exponent sum `0 > -1` given by `sum_filter_eq_zero_of_mem_Ioo`. A stronger form is `∃ L, EqOn (schwarzChristoffelBoundary a e z₀) L (Ioo p q) ∧ <the Edge conclusions about L>`. Then `injOn`, `collinear` and `continuousOn` follow from `EqOn.injOn_iff`, `Set.image_congr` and `ContinuousOn.congr`, with no manual `ext`. `sub_eq` becomes a rewrite with `EqOn`. A simpler alternative is to restate the Edge lemmas directly for the boundary map and drop the existential L.

Benefit: The limit-to-equality step is proved once and each call site becomes a short transfer through EqOn or Set.image_congr. The `collinear` proof loses its manual two-direction `ext`. Future edge results on the boundary map will not need to re-open the `∃ L` statements.

Source evidence:

- `TauCeti.collinear_schwarzChristoffelBoundary_image` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: convert hLcol using 1
  ext z
- `TauCeti.schwarzChristoffelBoundary_sub_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: rw [schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx),
    schwarzChristoffelBoundary_eq_of_tendsto a e z₀ y (hL y hy)]
- `TauCeti.continuousOn_schwarzChristoffelBoundary` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: refine hLcont.congr fun x hx => ?_
  exact schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)
- `limUnder lemma after exists_tendsto_schwarzChristoffelPrimitive_sub_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Infinity/Basic.lean`: obtain ⟨L, hL, -, -⟩ := exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀

### repeated-proof-machinery: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L96-L102)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`

The proof applies the cyclic Killing-form symmetry to the triple (γ, -α, β) and then skew-symmetry. This gives the Chevalley-free identity N(-α,-β)·B(xγ,x(-γ)) = -N(-α,γ)·B(xβ,x(-β)). Normalization.lean (`structureConstant_neg_add_mul_killingForm_eq`) repeats the same step. It builds the same two root-sum equations (`hγα` and `hαγ`/`hβγ`, each proved by `rw [Weight.coe_neg, hαβ]; abel`). It calls `structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ` and `structureConstant_skew (-α) γ β hβ _`. It then rewrites with both, and only afterwards uses `structureConstant_neg_neg_of_hom` to turn N(-α,-β) into -N(α,β). Both files re-derive the same intermediate fact, along with the `Weight.coe_neg`/`abel` side conditions. The calc in the target also repeats this relation inline, in the steps `rw [hcyc]` and `rw [hskew]`.

Proposed change:

Add one lemma in Symmetry.lean, which both files already import. It takes the same hypotheses as the target: hx, hβ, hγ and hαβ. It states `hx.structureConstant (-α) (-β) (-γ) hγ.neg _ * killingForm K L (x γ) (x (-γ)) = -(hx.structureConstant (-α) γ β hβ _ * killingForm K L (x β) (x (-β)))`. The root-sum equations are proved once, inside it. The target's calc then starts from this lemma, so `hcyc`, `hskew`, `hβγ` and `hγα` disappear and the two `rw` steps collapse into one. In Normalization.lean, `structureConstant_neg_add_mul_killingForm_eq` becomes: rewrite the helper with `hneg` and finish with `neg_mul`/`neg_inj`.

Benefit: The cyclic-then-skew derivation and its root-sum bookkeeping live in one place. Both consumers drop their copies of the setup. The Chevalley-free relation is stated explicitly, which makes it clear what Normalization.lean adds (only `hneg`) and what the target adds (only the root-length ratio).

Source evidence:

- `TauCeti.IsSl2System.structureConstant_neg_add_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: have hcyclic := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ
  have hskew := hx.structureConstant_skew (-α) γ β hβ hαγ
- `TauCeti.IsSl2System.structureConstant_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean`: hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ)) =

### repeated-proof-machinery: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L264-L278)

Declaration: `TauCeti.exists_forall_notMem_span_tangentVector (private)`

The argument finds a point off every line spanned by the tangent vectors. It forms F(s,t) = s • γ(t) on ℝ × ℝ, shows F is differentiable via differentiable_fst.smul (_ ∘ differentiable_snd), applies Differentiable.dense_compl_range_of_finrank_lt_finrank, and takes a point of the nonempty complement of the range. The same steps appear in exists_notMem_range_circle_sphere in Sphere.lean, with γ = fun t => (f (Circle.exp t) : E): the same F, the same differentiability proof, and the same density lemma. Each proof then unpacks the missing point with its own surjectivity-of-exp bookkeeping.

Proposed change:

Add one general lemma, for example `exists_forall_smul_ne_of_differentiable {γ : ℝ → V} (hγ : Differentiable ℝ γ) (hV : 2 < Module.finrank ℝ V) : ∃ a : V, ∀ s t, s • γ t ≠ a`. It would be proved once from F(s,t) = s • γ t. Here it would be applied to γ = deriv (f ∘ Circle.exp), and the span-membership step would use Submodule.mem_span_singleton. In Sphere.lean it would be applied to γ = fun t => (f (Circle.exp t) : E). There, a ≠ 0 follows by taking s = 0, which removes the separate `ha ⟨(0, 0), by simp [F]⟩` step, and the contradiction comes from s = ‖a‖. Both finrank hypotheses reduce to 2 < finrank: by simp for ℝ³ here, and by omega from finrank = n + 1 with 2 ≤ n there.

Benefit: The dimension-counting argument (the cone over a curve is the image of a plane) is proved and maintained in one place. Each call site then only unpacks its own conclusion, and the target proof shrinks to a few lines.

Source evidence:

- `TauCeti.exists_notMem_range_circle_sphere` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Geometry/Manifold/Instances/Sphere.lean`: let F : ℝ × ℝ → E := fun q => q.1 • (f (Circle.exp q.2) : E)
  have hF : Differentiable ℝ F := differentiable_fst.smul (hγ.comp differentiable_snd)
  obtain ⟨a, ha⟩ := (hF.dense_compl_range_of_finrank_lt_finrank
- `TauCeti.exists_forall_notMem_span_tangentVector` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: have hF : Differentiable ℝ F := differentiable_fst.smul (hd.comp differentiable_snd)

### repeated-proof-machinery: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L128-L140)

Declaration: `TauCeti.orbitRank_rigidSixGraph`

The proof that the orbit rank is at least 2 is the same generic argument as in `orbitRank_completeGraph_two_sum_three`. Both proofs rewrite `2 = 1+1` and turn `¬ rank ≤ 1` into a failure of orbit-stability at 1. They then pick a witness tuple that is equivalent at level 1 but not at level 2, and apply the stability hypothesis at level 2. The same unfolding chain (`Order.add_one_le_iff`, `lt_iff_not_ge`, `orbitRank_le_iff`, `mem_orbitStable_iff`) is written out twice. It is not specific to graphs or to the number 2.

Proposed change:

Add a lemma to Scott/Rank.lean along the lines of `orbitRank_eq_add_one_of_mem_orbitStable (a : Fin n → M) {γ} (hst : γ + 1 ∈ orbitStable a) (b) (hγ : BFEquiv γ n a b) (hne : ¬ BFEquiv (γ+1) n a b) : orbitRank a = γ + 1`. Its proof is `le_antisymm (orbitRank_le a hst)`, then `Order.add_one_le_iff` and `lt_iff_not_ge`, then `orbitRank_le_iff`, then `mem_orbitStable_iff`. In the final step the stability hypothesis is applied to `b`, `hγ` and `γ+1`. Both `orbitRank_rigidSixGraph` and `orbitRank_completeGraph_two_sum_three` would then reduce to `two_mem_orbitStable … ` plus a witness `w` with `bfEquiv_one …` and the negated level-2 equivalence. The γ = 1 case needs `(2:Ordinal) = 1 + 1`, which the callers already prove with `one_add_one_eq_two`.

Benefit: The ordinal and `sInf` bookkeeping is stated once, next to `orbitRank_le_iff`. Each graph example then shows only its graph-specific content, namely the level-one equivalence and the level-two separation. It also leaves a reusable tool for further Scott-rank examples.

Source evidence:

- `TauCeti.orbitRank_completeGraph_two_sum_three` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/CompleteGraphSum.lean`: rw [← one_add_one_eq_two, Order.add_one_le_iff, lt_iff_not_ge, orbitRank_le_iff,
    mem_orbitStable_iff]
  intro h
- `TauCeti.orbitRank_le_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/Rank.lean`: orbitRank (L := L) a ≤ α ↔ α ∈ orbitStable (L := L) a

### repeated-proof-machinery: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L114-L125)

Declaration: `TauCeti.two_mem_orbitStable_rigidSixGraph`

The orbit-stability proof is the same skeleton as in `two_mem_orbitStable` (CompleteGraphSum) and `orbitRank_le_natCard_sub_ncard_range` (Finite). Each unfolds `mem_orbitStable_iff` and intros `b h β`. Each then shows that `b` is the image of `a` under an automorphism (here the trivial one, `a = b`) and closes with `σ.bfEquiv β a` (here `BFEquiv.refl β a`). The rigid graph is the case where the only available `σ` is the identity.

Proposed change:

Add a lemma to Scott/Rank.lean such as `mem_orbitStable_of_exists_equiv (a : Fin n → M) (h : ∀ b, BFEquiv α n a b → ∃ σ : M ≃[L] M, σ ∘ a = b) : α ∈ orbitStable a`. Its proof is `intro b hb β; obtain ⟨σ, rfl⟩ := h b hb; exact σ.bfEquiv β a`. The Finite and CompleteGraphSum proofs would pass their existing `bfEquiv_iff_exists_equiv_comp_eq` and `bfEquiv_two_iff_exists_equiv…` results to it. The rigid-graph proof would pass `⟨1, …⟩`, using `hab` to show that the identity automorphism works. Alternatively, in this file use `rigidSixGraph_iso_eq_refl` to derive the orbit characterisation once.

Benefit: The three "orbit-stable because BF-equivalence implies being in one automorphism orbit" proofs share a single named step. Readers see directly that all three files use the same pattern: the BF class equals the orbit, so the class is stable.

Source evidence:

- `TauCeti.two_mem_orbitStable` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/CompleteGraphSum.lean`: obtain ⟨σ, rfl⟩ := (bfEquiv_two_iff_exists_equiv_completeGraph_two_sum_three a b).mp h
  exact σ.bfEquiv β a
- `TauCeti.orbitRank_le_natCard_sub_ncard_range` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/Finite.lean`: obtain ⟨σ, rfl⟩ := (bfEquiv_iff_exists_equiv_comp_eq (by omega)).mp h
  exact σ.bfEquiv β a

### repeated-proof-machinery: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L189-L248)

Declaration: `zero_mem_convexHull_of_best_approx (h_active, positive and negative branches)`

h_active proves the same small-ε estimate twice, once for f S = M with additiveFunction a S > 0 and once for f S = -M with additiveFunction a S < 0. Each branch unfolds additiveFunction, runs a long simp_all +decide only list, and then gives an explicit δ = M / (±∑ Λ(update 0 i 1)). It closes with nlinarith on mul_div_cancel₀. The two simp lists are nearly identical, and the arguments differ only by sign. The real-number fact underneath, that moving a value of absolute value M slightly in the direction that reduces |·| keeps it below M, is buried in the unfolded sums. The approach is fragile because it depends on the exact normal form simp produces.

Proposed change:

Prove one scalar lemma first, for example `lemma abs_sub_mul_lt_of_mul_pos {c x M : ℝ} (hM : 0 < M) (hc : |c| = M) (hcx : 0 < c * x) : ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, |c - ε * x| < M`. The proof takes δ = 2M/|x|, or splits on the sign of c once. In h_active, rewrite additiveFunction (fun i => ε' * a i) S as ε' * additiveFunction a S, using Finset.mul_sum once. Then apply the lemma with c = f S and x = additiveFunction a S. The hypothesis 0 < c * x follows from the pair (f S = M, a-sum > 0) or (f S = -M, a-sum < 0) by nlinarith or mul_pos / mul_pos_of_neg_of_neg. The two 30-line branches become one call after a short case split on eq_or_eq_neg_of_abs_eq.

Benefit: The analytic content is stated once with its real hypotheses. The simp-normal-form-dependent branches, which are hard to review, disappear. A reader sees directly why the perturbation moves f S into (-M, M), and proof maintenance no longer depends on the simp lemma lists.

Source evidence:

- `zero_mem_convexHull_of_best_approx (negative branch of h_active)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: div_pos hM_pos (h_additiveFunction_a_neg S hS_neg),

### repeated-proof-machinery: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L395-L435)

Declaration: `dual_cert_from_convexHull (h_sum_eq, the two mirrored rcases branches)`

Inside h_sum_eq, a generator v = S.indicator' or v = -S.indicator' must equal the sum of `if v = ±T.indicator' then v else 0` over the filtered finsets T. The two cases, f S = M and f S = -M, are proved by almost identical scripts. Each does rw [sum_eq_single S, sum_eq_zero] with the order swapped, runs a long simp +contextual only list, and then repeats a block that shows the two sums cannot both fire. That block does intro T hT₁ hT₂, congr_fun, a simp_all, ext a, and split_ifs at this. The same mirrored split also appears in the definitions of lam_pos and lam_neg, which are extracted separately. This is a fragile, copy-pasted argument.

Proposed change:

Factor the combinatorial fact into a lemma about the generators. For example, `lemma activeGenerators_decompose (hM_pos : 0 < M) {v} (hv : v ∈ activeGenerators f M) : v = ∑ S ∈ univ.filter (f · = M), if v = S.indicator' then v else 0 + ∑ S ∈ univ.filter (f · = -M), if v = -S.indicator' then v else 0`. The proof can use indicator'_injective and a single lemma that `-S.indicator' ≠ T.indicator'` for S, T whenever S.indicator' ≠ 0. Alternatively, parametrise by a sign σ ∈ {1, -1}, with generators σ • S.indicator', and prove the single-term sum once. Then use the lemma at the call site, so each rcases branch reduces to one application.

Benefit: The two near-duplicate 20-line scripts are replaced by one reusable statement. The disjointness of positive and negative generators becomes visible as a separate mathematical fact. This should shorten dual_cert_from_convexHull, which is currently very long, and make it easier to maintain.

Source evidence:

- `dual_cert_from_convexHull (first branch)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: · rw [Finset.sum_eq_single S, Finset.sum_eq_zero] <;>

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384-L424)

Declaration: `realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree (and the same pattern in other files)`

Both theorems repeat the same conversion from a weakly divergence-free `realPartVectorL2Representative z` to a weakly divergence-free `realVectorL2Representative (realPartVectorL2 z)`. It uses `realPartVectorL2Representative_eq_ae` and `isWeakDivFree_congr_ae`, and goes through a `change` that unfolds the definitions of `realLerayProjection` and `realStokesOperator`. The same conversion is also written out in `realHeatOperator_isInJ_of_fourierOrthogonal` and in `forcedMildCurve_mildJData`. So the argument appears in at least four places, two of them in this file. The file proves `realPart_isWeakDivFree_of_fourierOrthogonal` for the representative that is awkward to use, and each caller then has to transport the result by hand.

Proposed change:

Directly after `realPartVectorL2Representative_eq_ae`, add one lemma stating `∀ (v : ComplexVectorL2), (∀ᵐ ξ ∂volume, inner ℂ (complexifyFrequency ξ) ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) v ξ) = 0) → CKN.IsWeakDivFreeL2 (realVectorL2Representative (realPartVectorL2 v))`. Prove it with `isWeakDivFree_congr_ae (realPartVectorL2Representative_eq_ae v).symm (realPart_isWeakDivFree_of_fourierOrthogonal v hv)`. The two `realXxx_isWeakDivFree` theorems then reduce to this lemma plus their Fourier-orthogonality `filter_upwards` argument. The heat and forced-solution call sites can use it too. Alternatively, restate `realPart_isWeakDivFree_of_fourierOrthogonal` for the `realVectorL2Representative (realPartVectorL2 v)` form.

Benefit: This removes the repeated `change`/`congr_ae` boilerplate at four call sites. It also gives one named statement for the common use, "Fourier-orthogonal complex field gives a weakly div-free real part". It also makes the `*Representative_isWeakDivFree` intermediate theorems unnecessary where they exist only to be converted.

Source evidence:

- `realHeatOperator_isInJ_of_fourierOrthogonal` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierHeatDivergence.lean`: have h := realPartVectorL2Representative_eq_ae sh
- `forcedMildCurve_mildJData` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedSolutionJ.lean`: (isWeakDivFree_congr_ae (realPartVectorL2Representative_eq_ae _).symm hweak)

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364-L413)

Declaration: `realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree`

Both proofs run the same argument. They state that the Fourier transform of the operator output equals the multiplier applied to the transformed input, using `change ℱ (ℱ.symm …) = _` and `apply_symm_apply`. They then take `Lp.ext_iff` to get an a.e. identity, and `filter_upwards` against the multiplier's a.e. divergence-free lemma, then `rw [hξ]; exact hrange`. The same `ℱ (ℱ.symm m) = m` computation for Leray and Stokes is repeated in other files, for Stokes in `RegularisedBesselStokesPhysical` and for the heat semigroup in `FourierHeatDivergence`. It is also redone for Leray inside `ForcePressureOrthogonality`.

Proposed change:

Add the two small named identities `fourier_lerayProjectionL2 (v) : ℱ (lerayProjectionL2 v) = lerayFourierMultiplier (ℱ v)` and `fourier_stokesL2Operator ht F : ℱV (stokesL2Operator ht F) = stokesFourierMultiplier ht (ℱT F)`. Put them next to the definitions in `FourierLeray.lean`. Each is `ℱ.apply_symm_apply _`. Then add a single lemma, "if `ℱ v =ᵐ g` and `g` is a.e. frequency-orthogonal, then `v` is". Both theorems here reduce to it, and the other files can rewrite with the two identities.

Benefit: The Fourier-side bookkeeping is stated and proved once, where the operators are defined. The two theorems here become short. The other call sites also lose their local `change`/`apply_symm_apply` blocks.

Source evidence:

- `hStokesFourier (local have)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/RegularisedBesselStokesPhysical.lean`: change ℱV (ℱV.symm (stokesFourierMultiplier ht (ℱT G))) = _
    exact ℱV.apply_symm_apply _
- `heatSemigroup_preserves_fourierOrthogonal (local htransform)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierHeatDivergence.lean`: change ℱ (ℱ.symm (heatMultiplier t ht • ℱ v)) = _
    exact ℱ.apply_symm_apply _

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L342-L441)

Declaration: `pv_cutoff_F_integrable_delta_1, pv_cutoff_F_integrable_1_2, pv_cutoff_F_integrable_2_3delta, pv_cutoff_integral_seg1_eq_inv, pv_cutoff_integral_seg2_eq_Ialpha, pv_cutoff_integral_seg3_eq_neg_inv`

The same pointwise computation of the cutoff integrand F on the open segments is proved in six places. Each integrability lemma has an `h_eq` block. Each integral lemma has an almost identical `h_on_Ioo` block. For example, segment 3 appears at lines 412–425 and 557–570, and segment 1 at lines 358–363 and 504–513. Every copy unfolds F, rewrites with `sectorCurve_segN` and `deriv_sectorCurve_segN`, runs `field_simp` for the case ‖γ t‖ > ε, and proves ε < ‖γ t‖ by `calc ε = δ * r … nlinarith` for the other case. SectorCurveLemma.lean repeats it a third time for `cauchyPrincipalValueIntegrand'`, in `cauchyPV_inv_integrableOn_δ1`, `_12` and `_2_3δ`. The `pv_integrand_seg1/2/3` lemmas already give the unconditional integrand values. The cutoff condition is the only extra step.

Proposed change:

Add three lemmas giving the cutoff integrand on each open segment, for 0 < ε < r with δ = ε / r. For segment 1, F t = ↑(t⁻¹) for t ∈ Ioo (ε/r) 1. For segment 2, F t = I * ↑α for t ∈ Ioo 1 2. For segment 3, F t = -↑((3 - t)⁻¹) for t ∈ Ioo 2 (3 - ε/r). State them for a named `def` of the cutoff integrand, or for `cauchyPrincipalValueIntegrand' (fun z => z⁻¹) (sectorCurve r α) 0 ε`, so that SectorCurveLemma.lean can reuse them. Each segment lemma uses `pv_integrand_seg*` for the true branch and the norm lemmas `sectorCurve_norm_seg1`, `sectorCurve_norm_on_arc` and `sectorCurve_norm_seg3'` for the false branch. All six proofs in this file, and the three in SectorCurveLemma.lean, then just instantiate these lemmas.

Benefit: This removes roughly 60 lines of duplicated `field_simp` / `nlinarith` reasoning in this file, and more in SectorCurveLemma.lean. A fix to one case no longer has to be copied to the others. The integrability and integral proofs then show only what is specific to them, namely continuity of the model function or `integral_congr_ae`.

Source evidence:

- `pv_cutoff_integral_seg3_eq_neg_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_on_Ioo : ∀ t ∈ Ioo 2 (3 - δ), F t = -(↑((3 - t)⁻¹) : ℂ) := by
- `pv_cutoff_integral_seg1_eq_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
- `pv_cutoff_integral_seg2_eq_Ialpha` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_on_Ioo : ∀ t ∈ Ioo 1 2, F t = I * ↑α := by
- `cauchyPV_inv_integrableOn_2_3δ` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: -(↑((3 - t)⁻¹) : ℂ) := fun t ⟨ht2, ht3δ⟩ => by
- `cauchyPV_inv_integrableOn_δ1` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: rw [ite_eq_left]; · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L593-L610)

Declaration: `pv_cutoff_F_integrable_0_delta, pv_cutoff_F_integrable_3delta_3, pv_sector_cutoff_eq (hI1, hI5)`

The fact that F vanishes on [0, δ] and on [3 − δ, 3] is proved twice for each end in this file. Once as `IntervalIntegrable` via `intervalIntegrable_const.congr`, at lines 317–322 and 334–340. Once as `integral = 0` via `integral_congr` to the zero integrand, at lines 593–600 (`hI1`) and 602–610 (`hI5`). Each copy shows that the cutoff condition is false because ‖γ t‖ ≤ ε, using the same norm lemma and the same `δ * r = ε` field_simp. SectorCurveLemma.lean again repeats this in `cauchyPV_inv_integrableOn_0δ` and `_3δ3`.

Proposed change:

Prove once that for 0 < ε < r, F t = 0 for t ∈ Icc 0 (ε/r) and for t ∈ Icc (3 - ε/r) 3. The Ioc cases follow from these because Ioc ⊆ Icc. Then `pv_cutoff_F_integrable_0_delta` and `_3delta_3` become `(intervalIntegrable_const …).congr` applied to the lemma, and `hI1` and `hI5` become `integral_congr` applied to it followed by `integral_zero`. Alternatively, drop the separate integrability statements for the two end pieces by integrating over [0,δ] and [3−δ,3] directly with the lemma.

Benefit: The norm estimate and the δ * r = ε bookkeeping are written once instead of four times in this file (and twice more in SectorCurveLemma.lean). The main theorem `pv_sector_cutoff_eq` becomes shorter and its structure is easier to see.

Source evidence:

- `pv_cutoff_F_integrable_0_delta` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1, le_trans ht.2 (le_of_lt hδ1)⟩]
- `pv_cutoff_F_integrable_3delta_3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
- `pv_sector_cutoff_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
- `cauchyPV_inv_integrableOn_0δ` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt ht.1,

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288-L297)

Declaration: `log_cancellation`

`log_cancellation` re-proves, inline, the two real integral evaluations that are stated just above it as `integral_seg1_eq_neg_log` (lines 255–257) and `integral_seg3_eq_log` (lines 260–268). The `h_sub` argument with `integral_comp_sub_left`, `congr 1 <;> ring` and `simp_all` is copied verbatim with ε replaced by ε / r. `h1` redoes `integral_inv_of_pos` and `Real.log_div`. The earlier lemmas are not used.

Proposed change:

Specialise the existing lemmas at ε / r: `h1 := integral_seg1_eq_neg_log (ε / r) hεr_pos hεr_lt1` and `h2 := integral_seg3_eq_log (ε / r) hεr_pos hεr_lt1`. Both have exactly the shapes of `h1` and `h2` in `log_cancellation`. Delete `h_sub` and the inline rewriting. The complex-cast steps `h1c` and `h2c` stay as they are.

Benefit: This removes about ten lines of duplicated argument and gives the earlier lemmas a use. A reader sees that the cancellation is just the two standard log integrals.

Source evidence:

- `integral_seg3_eq_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h1 : ∫ t in (2 : ℝ)..(3 - ε), (3 - t)⁻¹ = ∫ u in ε..1, u⁻¹ := by
- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428)

Declaration: `norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le`

The first- and second-derivative decay bounds repeat the same three-part argument. (1) The phase bound exp((σ-1/2)x) ≤ exp(a|x|) is proved by le_abs_self plus simp_all. (2) Norms of terms of the form (r:ℂ)*exp((σ-1/2)x) are unfolded by the same long simp only [norm_mul, Complex.norm_real, …] followed by norm_num and the hnorm rewrite of ‖(σ:ℂ)-1/2‖ = a. (3) The finish is P*exp(-δx²)*exp(a|x|) ≤ exp(a²/(2δ))*(P*exp(-(δ/2)x²)) via Real.exp_add, ring and exp_neg_mul_sq_add_mul_le. The second proof (about 190 lines) also restates the nonnegativity of the polynomial P twice. The calc chains are hard to follow, and any change to the phase or Gaussian-shift argument has to be made in both places.

Proposed change:

Add two small private lemmas before the first bound. (a) For a = |σ-1/2|: exp((σ-1/2)*x) ≤ exp(a*|x|). (b) For 0 ≤ P and 0 < δ: P*exp(-δ*x^2)*exp(a*|x|) ≤ exp(a^2/(2*δ))*(P*exp(-(δ/2)*x^2)), proved from Real.exp_add and exp_neg_mul_sq_add_mul_le. Optionally add (c): ‖(r:ℂ)*exp((σ-1/2)*x)‖ = |r|*exp((σ-1/2)*x), and the same with an extra factor (σ-1/2). Each bound then only does the triangle inequality and the real polynomial estimate, and ends with (b), where the polynomial P is stated once and its nonnegativity is proved once.

Benefit: This removes a long duplicated tail from both proofs, so each states only its real-variable polynomial estimate. It also makes the shared role of the Gaussian-shift step visible, and any later third-derivative bound can reuse it.

Source evidence:

- `norm_poitouVerticalProfileSecondDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:           (exp_neg_mul_sq_add_mul_le hδ a x) hP
- `norm_poitouTransformIntegrand_regularizedScaledTartar_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean`:         exp_neg_mul_sq_add_mul_le hδ |s.re - 1 / 2| x

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L436-L449)

Declaration: `poitouVerticalProfileDerivative_regularized_integrable (hone) vs integrable_quadratic_abs_mul_exp_neg_mul_sq`

The first-derivative integrability proof builds its majorant K*(A*e^{-(δ/2)x²}) + K*(2δ*(|x|*e^{-(δ/2)x²})) by hand. It proves integrability of |x|*exp(-b x²) from integrable_mul_exp_neg_mul_sq.norm, using simp_all. The later helper integrable_quadratic_abs_mul_exp_neg_mul_sq proves the same facts for (A + B|x| + C x²)*exp(-b x²), with the same hzero/hone steps. The same |x|*exp moment argument also appears in RegularizedTartarTransform (hmoment). The general helper is stated after its first use, so the first proof could not reuse it.

Proposed change:

Move integrable_quadratic_abs_mul_exp_neg_mul_sq above poitouVerticalProfileDerivative_regularized_integrable, or into RegularizedTartarTransform. In the first-derivative proof, take hmajor := (integrable_quadratic_abs_mul_exp_neg_mul_sq (half_pos hδ) A (2*δ) 0).const_mul K. Then apply hmajor.mono' with the same measurability argument. The pointwise bound needs a small ring/grind step to absorb 0 * x^2. This deletes hzero and hone. Optionally extract the |x|*exp(-b x²) integrability as its own lemma for the other two copies.

Benefit: The Gaussian-moment integrability argument is proved once, and the first- and second-derivative integrability proofs then have the same shape. That is easier to read and to maintain.

Source evidence:

- `integrable_quadratic_abs_mul_exp_neg_mul_sq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:     have h := (integrable_mul_exp_neg_mul_sq hb).norm.const_mul B
- `hasDerivAt_poitouTransform_regularizedScaledTartar` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean`:     have h := (integrable_mul_exp_neg_mul_sq (half_pos hδ)).norm

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1180-L1210)

Declaration: `fourier_poitouVerticalProfileDerivative_regularized / fourier_poitouVerticalProfileSecondDerivative_regularized`

The two theorems (556–579 and 1180–1210) have the same proof. Each states a hderiv equation `deriv g = g'` by funext, calls Real.fourier_deriv with the integrability of g, differentiability of g, and integrability of deriv g rewritten via hderiv, applies congrFun at w, and closes with simp_all. Only the function pair (g, g') differs. The deriv_*/differentiable_* wrapper lemmas exist solely to feed this pattern, and each call site re-states the long regularizedScaledTartar arguments.

Proposed change:

Add one general lemma: for g g' : ℝ → ℂ with Integrable g, Integrable g' and ∀ x, HasDerivAt g (g' x) x, we get 𝓕 g' w = (2 * Real.pi * I * w) • 𝓕 g w. Prove it once, by deriving deriv g = g' from the HasDerivAt hypotheses and applying Real.fourier_deriv. Both fourier_… theorems then follow by passing the existing hasDerivAt_poitouVerticalProfile (with hasDerivAt_regularizedScaledTartar) and hasDerivAt_regularizedPoitouVerticalProfileDerivative, plus the two integrability facts. This also lets the deriv_regularizedPoitouVerticalProfile* wrappers be dropped if nothing else uses them, apart from the aestronglyMeasurable step at line ~1145.

Benefit: The Fourier-derivative identity and its simp_all closing step appear once, and the instance theorems become short and obviously parallel. The separate hderiv/funext boilerplate disappears.

Source evidence:

- `fourier_poitouVerticalProfileDerivative_regularized` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:     congrFun (Real.fourier_deriv
      (regularizedPoitouVerticalProfile_integrable hδ σ)

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L128)

Declaration: `exists_positive_shell`

This is the same dyadic-index argument that appears in Kernel.lean as exists_shell_of_pos_lt, and twice more in Hedberg.lean as nearShell_cover and farShell_cover. In each copy it sets x = ρ/R and k = ⌊log x / log 2⌋. It proves 2^k ≤ x < 2^(k+1) by applying strict monotonicity of log, Real.log_rpow and field_simp. It then turns that into 2^k R ≤ ρ < 2^(k+1) R. Only the final step differs: showing k ≥ 0, showing k < 0, or converting k to ℕ. Roughly 30 lines are copied each time. Mathlib already has Int.zpow_log_le_self and Int.lt_zpow_succ_log_self (in Mathlib/Data/Int/Log.lean), which give this two-sided dyadic bound directly.

Proposed change:

Add one shared lemma in Kernel.lean, next to mem_parabolicRieszShell. For 0 < R and R ≤ ρ (or 0 < ρ in general), it would return ∃ k : ℤ, (2:ℝ)^(k:ℝ) * R ≤ ρ ∧ ρ < (2:ℝ)^((k:ℝ)+1) * R. Prove it from Int.log 2 (ρ/R), Int.zpow_log_le_self, Int.lt_zpow_succ_log_self and Real.rpow_intCast. Equivalently, state it as ∀ w, 0 < ρ(z,w) → ∃ k : ℤ, w ∈ parabolicRieszShell R k z. Then redo exists_positive_shell and exists_shell_of_pos_lt as short wrappers. The wrappers only add the sign facts k ≥ 0 (from 1 ≤ ρ/R) or k < 0 (from ρ/R < 1) and, for the positive case, the toNat conversion. Hedberg.lean's farShell_cover and nearShell_cover could use the same pattern.

Benefit: This removes three or four near-identical 30-line log/floor proofs and leaves one short proof of the dyadic bound. Each caller then states only its own sign condition. The log/floor case analysis is easier to audit once than in four copies.

Source evidence:

- `CKN.Foundation.Parabolic.Morrey.exists_shell_of_pos_lt` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: let k : ℤ := ⌊Real.log x / L⌋
- `farShell_cover` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean`: have hkhi : Real.log x / L < (k : ℝ) + 1 := Int.lt_floor_add_one _
- `nearShell_cover` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean`: have hkneg : k < 0 := by
- `Int.lt_zpow_succ_log_self` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Data/Int/Log.lean`: theorem lt_zpow_succ_log_self {b : ℕ} (hb : 1 < b) (r : R) : r < (b : R) ^ (log b r + 1)

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L168-L190)

Declaration: `ennreal_mul_rpow`

This repeats a roughly 20-line proof, which is identical to the one in Hedberg.lean (ennreal_mul_rpow_of_ne_zero_of_ne_top). Both reprove (x*y)^e = x^e*y^e for any real e by splitting on the sign of e and inverting. Mathlib already has ENNReal.mul_rpow_of_ne_zero (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ), and ENNReal.mul_rpow_of_ne_top for the finite case. Here the hypotheses (hxtop, hy0, hytop) are not needed, and hy0 and hytop are bound to `_`.

Proposed change:

Delete ennreal_mul_rpow. In positive_shell_scale_identity, use ENNReal.mul_rpow_of_ne_zero hSn0 hT0 _ and ENNReal.mul_rpow_of_ne_zero hSn2_0 hT0 _, or ENNReal.mul_rpow_of_ne_top hSnTop hTTop _. Then the hSnTop and hSn2_Top facts can be dropped if the ne_zero version is used. Delete the Hedberg copy in the same way.

Benefit: This removes about 23 lines of proof here and about as many in Hedberg.lean. It also removes a private lemma with unused hypotheses, and the call sites then rely on a recognised library lemma.

Source evidence:

- `ENNReal.mul_rpow_of_ne_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`: theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z
- `ennreal_mul_rpow_of_ne_zero_of_ne_top` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Euclidean/Hedberg.lean`: private lemma ennreal_mul_rpow_of_ne_zero_of_ne_top

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L160)

Declaration: `positiveShell_pairwise`

The disjointness of parabolic Riesz shells is proved separately three times. The proofs are in positiveShell_pairwise here, in negativeShell_pairwise and pairwise_disjoint_parabolicRieszShells in Kernel.lean, and in heatPotential_far_shells_pairwise_disjoint in SubordinatedBase.lean. Each proves the same fact: for integers k < l, the shells are disjoint because 2^(k+1) R ≤ 2^l R. Each does this with two nearly mirrored branches: it casts k+1 ≤ l to ℝ, applies rpow_le_rpow_of_exponent_le, multiplies by R, and contradicts the upper bound of one shell with the lower bound of the other. Only the index arithmetic (ℕ, Int.negSucc, j+6, subtype) differs.

Proposed change:

Prove one lemma in Kernel.lean next to parabolicRieszShell, say for 0 < R and k < l : ℤ, Disjoint (parabolicRieszShell R k z) (parabolicRieszShell R l z). Derive both orderings from it with Disjoint.symm. Then positiveShell_pairwise becomes `Pairwise.mono`-style or `fun n m h => ...`, using Nat.cast_lt and Int.negSucc ordering by omega. Similar one-line wrappers cover the other three proofs.

Benefit: This replaces four sets of mirrored branches, each about 20 lines, with one shared lemma plus short index-translation wrappers. The shell geometry is stated once, and each caller only handles its own indexing.

Source evidence:

- `negativeShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
- `pairwise_disjoint_parabolicRieszShells` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hpow hR.le).trans
- `heatPotential_far_shells_pairwise_disjoint` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedBase.lean`: exact (not_lt_of_ge (hrad.trans hwk.1)) hwj.2

### repeated-proof-machinery: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L195-L244)

Declaration: `RS.AnalyticAt.exists_taylor_remainder`

The Taylor remainder factorization, G = (degree-<m Taylor polynomial) + (z - z₀)^m * (analytic r) built from the m-fold iterated dslope, is proved here and again in a separate file. `taylor_remainder_factored` in MeromorphicPrincipalPart.lean states the same fact with the Taylor polynomial written via `iteratedDeriv k G s / k!`. Its proof is a long power-series calculation: `hasFPowerSeriesAt_iff'`, `hasSum_nat_add_iff'`, `tsum_mul_left`, and `set` blocks. It uses the same `(Function.swap dslope s)^[N] G` remainder and the same `has_fpower_series_iterate_dslope_fslope` analyticity fact. The two statements differ only in the coefficient presentation and the pointwise-versus-eventual quantifier. The target's version is strictly stronger, since it holds for every z and also gives the remainder's coefficients. The two proofs of one mathematical argument need separate maintenance, and the unreferenced second copy is not explained by any shared result.

Proposed change:

Make `RS.AnalyticAt.exists_taylor_remainder` (or a small corollary of it) the single source of this factorization. Prove `taylor_remainder_factored` from it. Take `r` and the pointwise identity `g z = ∑ d ∈ range m, taylorCoeffAt g z₀ d * (z - z₀)^d + (z - z₀)^m * r z` from the target lemma, and rewrite `taylorCoeffAt g s d` as `iteratedDeriv d G s / d!` using `HasFPowerSeriesAt.taylorCoeffAt_eq` with the `ofScalars` series that file already builds (`pG`). Then delete the ~30-line tsum computation. Alternatively, move the factorization into a shared file below both users. This depends on the LeanModularForms file being able to import the ResidueCalculus layer without a cycle.

Benefit: One proof of the Taylor remainder factorization remains. The 30-line `hasSum`/`tsum` computation disappears from the principal-part file, and later changes to the statement need to be made only once. A reader meets a single canonical statement, with an exact pointwise identity rather than an eventual one.

Source evidence:

- `taylor_remainder_factored` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicPrincipalPart.lean`: ∀ᶠ z in 𝓝 s, G z - P z = (z - s) ^ N • H z
- `taylor_remainder_factored` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicPrincipalPart.lean`: have hH_fps := HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope N hG_fps
- `RS.AnalyticAt.exists_taylor_remainder` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: ∀ z, g z = (∑ d ∈ Finset.range m, taylorCoeffAt g z₀ d * (z - z₀) ^ d)
- `RS.HasFPowerSeriesAt.taylorCoeffAt_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: taylorCoeffAt g z₀ j = p.coeff j

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188-L263)

Declaration: `weakPathRepresentative_pairing_eq_inner / FrozenDriftProblem.initial_pairing_eq_cell_integral`

Two long proofs carry out the same argument. First, the unit-cube integral of a product φ·ψ is rewritten to the unit-cell integral and then to the torus integral of periodicToTorus (φ·ψ). The periodicToTorus of the product is then identified with the product of the periodicToTorus values, and the two L² classes are replaced by their representatives using a.e. equalities. Finally the integral is converted to `L2.inner_def` using `simp [mul_comm]`. The first theorem runs this chain in reverse with φ = weakPathRepresentative u t and the class u t. The second runs it forward with φ = P.θ₀ and the class P.initialTorusL2. The `show ... from rfl` product-splitting step, the `integral_congr_ae`/`mul_comm` step and the `L2.inner_def` step are duplicated verbatim in shape. The chain exists only as two separate calc blocks.

Proposed change:

Add one helper in this file. It takes f g : ScalarTorusL2 and φ ψ : Vec 2 → ℝ, with hf : (fun x : Torus => f x) =ᵐ[volume] periodicToTorus φ and hg : (fun x : Torus => g x) =ᵐ[volume] periodicToTorus ψ. It concludes `inner ℝ f g = ∫ x in AVenhance.unitCube, φ x * ψ x`. Prove it once by the existing calc, using `L2.inner_def`, `integral_congr_ae` with `filter_upwards [hf, hg]`, `integral_periodicToTorus_eq_unitCell` and `integral_unitCell_eq_unitCube`. Then `initial_pairing_eq_cell_integral` is the helper applied to the two `coeFn_toLp` facts it already proves, namely hθ and hψT. `weakPathRepresentative_pairing_eq_inner` is the helper (symm) applied to the pointwise identity htheta, turned into an a.e. statement with `Filter.Eventually.of_forall`, and to the `coeFn_toLp` fact htest. Both call sites reduce to establishing the representative equalities. The helper covers both cases, because the first needs only a.e. equality for f and the second gets it from `coeFn_toLp`.

Benefit: The measure-theoretic bookkeeping (cell versus cube, product of periodicToTorus values, inner product as integral) is proved once. Each theorem then shows only what is specific to it: the weak-path representative, or the datum. A change to the torus transfer lemmas needs one edit instead of two, and the helper statement documents the bridge between torus L² pairing and the unit-cube integral.

Source evidence:

- `FrozenDriftProblem.initial_pairing_eq_cell_integral` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: filter_upwards [hθ, hψT] with x hx hψx

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184)

Declaration: `weakPathRepresentative_isPeriodic / weakPathRepresentative_memL2On / weakPathRepresentative_l2NormSq / weakPathRepresentative_pairing_eq_inner`

The same unfolding argument, showing that for t in Icc 0 1 the weak path representative is scalarTorusRepresentative (u ⟨t,_⟩), is reproved inline four times. It appears in the periodicity proof (the `ht` case), in memL2On, in l2NormSq, and as `hrep` inside the pairing theorem. Each time it uses `funext` and `simp [weakPathRepresentative, …]`. It is short, but it is repeated at four call sites and obscures the structure of each proof.

Proposed change:

Add `theorem weakPathRepresentative_of_mem (u) (t : Icc (0:ℝ) 1) : weakPathRepresentative u t = scalarTorusRepresentative (u t)`, stated for the subtype coercion, and use it in all four places. The periodicity proof's membership case would use it via `⟨t, ht⟩`. memL2On and l2NormSq then become `rw [weakPathRepresentative_of_mem]; exact …`. The pairing theorem's `hrep` is replaced by the lemma.

Benefit: This removes four duplicated sub-proofs, so the three downstream bridge lemmas become one-liners. It also gives a reusable simp/rw lemma for the later weak-solution assembly mentioned in the module docstring.

Source evidence:

- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: have hrep : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by

### repeated-proof-machinery: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L134-L169)

Declaration: `bivariateEquiv_symm_natDegree_eq_degreeOf_one`

This theorem rebuilds the argument that the outer degree of the plane-curve presentation of f is degreeOf 1 f. It checks ringHom_ext on constants and X 0 / X 1, then pushes natDegree through an injective coefficient map. The repo already proves the same statement elsewhere. planeCurvePolynomialInSecondCoordinate_natDegree gives natDegree = degreeOf 1 f for the swap-composite equivalence, and planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv identifies that equivalence with (Polynomial.Bivariate.equivMvPolynomial K).symm. PlaneCurveFunctionField.lean (polynomialOverFirstCoordinate_eq_map_polynomialInSecondCoordinate and natDegree_polynomialOverFirstCoordinate_le_degreeOf_second) repeats the optionEquivLeft/rename/ringHom_ext setup a third time.

Proposed change:

Delete the ad hoc proof. Prove the statement as `rw [← planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv]; exact planeCurvePolynomialInSecondCoordinate_natDegree f`. If the target cannot import PlaneCurveLocalReciprocalDiscriminant, move planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv down next to the definition in PlaneCurveDiscriminantBound. Alternatively, keep a single shared natDegree lemma for the optionEquivLeft presentation and use it from both files.

Benefit: The optionEquivLeft/Unique-subtype/ringHom_ext argument then exists once. The target no longer needs the Unique-instance and subtype-index bookkeeping, and later edits to the presentation need only one proof change.

Source evidence:

- `planeCurvePolynomialInSecondCoordinate_natDegree` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveDiscriminantBound.lean`: (planeCurvePolynomialInSecondCoordinate f).natDegree =
      MvPolynomial.degreeOf 1 f
- `planeCurvePolynomialInSecondCoordinate_eq_bivariateEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean`: planeCurvePolynomialInSecondCoordinate f =
      (Polynomial.Bivariate.equivMvPolynomial K).symm f
- `polynomialOverFirstCoordinate_eq_map_polynomialInSecondCoordinate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveFunctionField.lean`: (MvPolynomial.optionEquivLeft K {i : Fin 2 // i ≠ 1}).toRingEquiv.toRingHom.comp

### repeated-proof-machinery: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L50-L99)

Declaration: `planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C`

These three simp lemmas have the same proofs as planeCurvePolynomialInSecondCoordinate_X_zero, _X_one and _C in PlaneCurveLocalReciprocalDiscriminant.lean. Each computes finSuccEquiv on X 0, X 1 and C c, rewrites with finSuccEquiv_apply, uses `show (1 : Fin 2) = Fin.succ 0 by decide` plus `rfl`, then maps through uniqueAlgEquiv. The two presentations differ only by a coordinate swap, so the finSuccEquiv-then-uniqueAlgEquiv computations are shared. The transpose lemma `transposeBivariate_planeCurveToBivariate` in the target already connects the two orientations.

Proposed change:

State the finSuccEquiv/uniqueAlgEquiv generator computations once, for a common map such as (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1))).trans-composed with finSuccEquiv. Derive both families of simp lemmas from it. Alternatively, define planeCurveToBivariate as `planeCurvePolynomialInSecondCoordinate` followed by transposition and obtain the lemmas from the existing ones. Then planeCurveToBivariate_natDegree_eq_degreeOf_zero and the transposition lemma could also be shortened.

Benefit: This removes about 50 lines of near-duplicate calc/change/rw proofs in two files, and one set of generator facts then serves both orientations.

Source evidence:

- `planeCurvePolynomialInSecondCoordinate_X_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean`: rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
- `planeCurvePolynomialInSecondCoordinate_C` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean`: MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c)

### repeated-proof-machinery: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L219-L259)

Declaration: `evalBivariate_planeCurveFrobeniusRelation`

The proof shows that evaluating the iterated presentation at (x, y) equals eval₂ of the original polynomial. It builds lhs and rhs ring homomorphisms from MvPolynomial (Fin 2) K, runs ringHom_ext, checks constants and fin_cases on the two coordinates. This is the argument of eval₂_planeCurvePolynomialInSecondCoordinate in PlaneCurveLocalReciprocalDiscriminant.lean, which is already stated for an arbitrary K-algebra A. Here it is redone for planeCurveToBivariate F with a coefficient map ι, specialized to A = L.

Proposed change:

Prove one general lemma for planeCurveToBivariate over an arbitrary commutative semiring A with an algebra structure. For example, it could say eval₂ (eval₂RingHom (algebraMap K A) y) x (planeCurveToBivariate K f) = MvPolynomial.eval₂ (algebraMap K A) ![x, y] f. Alternatively, reuse eval₂_planeCurvePolynomialInSecondCoordinate through transposeBivariate_planeCurveToBivariate and an evaluation-transposition lemma. Obtain evalBivariate_planeCurveFrobeniusRelation from it with A = L, the base-change map ι, and `MvPolynomial.eval₂_map` together with `coe_perfectConstantsToFrobeniusSubfield`.

Benefit: The generator-by-generator evaluation check is stated once. The Frobenius-specific lemma then reduces to the one fact that ι agrees with algebraMap K L, and the long `change`/`simp only` constant case disappears.

Source evidence:

- `eval₂_planeCurvePolynomialInSecondCoordinate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveLocalReciprocalDiscriminant.lean`: Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K A) x) y
        (planeCurvePolynomialInSecondCoordinate f) =
      MvPolynomial.eval₂ (algebraMap K A) ![x, y] f

### repeated-proof-machinery: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L79-L88)

Declaration: `EulerMeanHarmonic.localL2Energy_ball_le_of_ae_bound`

This proof repeats the argument in `harmonic_smallBall_energy`. In both, an integral over `Metric.ball 0 r` is bounded by a constant using `integral_mono_ae` or `setIntegral_mono_on` with `integrableOn_const measure_ball_lt_top.ne`. The constant integral is then rewritten with `setIntegral_const`, `smul_eq_mul`, a `change` to `(volume (ball 0 r)).toReal * _`, and `volume_ball_toReal`, and closed with `ring`. Only the integrand, the constant, and the source of integrability differ. The 3D ball-volume computation is therefore inlined twice, and a change to how the ball volume is handled would need two matching edits.

Proposed change:

Add a helper next to `volume_ball_toReal` in MeanHarmonicSmallBall.lean. It would say: for `f : Space → ℝ`, `0 ≤ r`, `IntegrableOn f (Metric.ball 0 r)` and `∀ᵐ x ∂volume, x ∈ Metric.ball 0 r → f x ≤ C`, we get `∫ x in Metric.ball (0:Space) r, f x ≤ (Real.pi * 4 / 3) * r^3 * C`. Its proof would be the current calc. `localL2Energy_ball_le_of_ae_bound` then becomes the helper applied to `integrable_norm_sq_L2 u |>.integrableOn`. `harmonic_smallBall_energy` becomes the helper applied to `hi.integrableOn` and the pointwise bound, followed by the `harmonicSmallBallConstant` unfolding and `ring`. The ae form covers the harmonic site, whose pointwise `hbound` is a special case.

Benefit: The ball-volume and constant-integral computation sits in one place. Each caller reduces to supplying integrability and a pointwise bound, so its statement-specific content is easier to see.

Source evidence:

- `EulerMeanHarmonic.harmonic_smallBall_energy` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanHarmonicSmallBall.lean`: rw [setIntegral_const, smul_eq_mul]
      change (volume (Metric.ball (0 : Space) r)).toReal * _ = _
      rw [volume_ball_toReal r hr]
- `EulerMeanHarmonic.harmonic_smallBall_energy` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanHarmonicSmallBall.lean`: apply setIntegral_mono_on hi.integrableOn (integrableOn_const (measure_ball_lt_top.ne))
