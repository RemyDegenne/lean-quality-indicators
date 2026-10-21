# Findings

### concept-reinvention: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L63-L81)

Declaration: `Algebra.TensorProduct.basis (with basisAux, basisAux_tmul, basisAux_map_smul, basis_repr_tmul, basis_apply, basis_repr_symm_apply, basis_repr_symm_apply')`

This file builds the A-basis of `A ⊗[R] M` induced by an R-basis of `M` from scratch. Mathlib already has `Module.Basis.baseChange`, which builds the same basis under the same hypotheses: `S` a `Semiring` with an `R`-algebra structure, and `b : Basis ι R M`. It comes with the same simp API: `baseChange_apply : b.baseChange S i = 1 ⊗ₜ b i` and `baseChange_repr_tmul`. The two bases therefore have separate constructions, separate `basis_apply`/`baseChange_apply` lemmas and separate repr lemmas. Downstream files use both: Trace.lean uses `Algebra.TensorProduct.basis`, while the Kaehler and Cotangent files use `Basis.baseChange`. Even this file shows the clash: it adds `Module.Basis.baseChange_linearMap` and `Module.Basis.baseChange_end` in the `Basis.baseChange` namespace, but states them for `Algebra.TensorProduct.basis`.

Proposed change:

Make one construction canonical. The simplest option is to define `Algebra.TensorProduct.basis A b` as `b.baseChange A`, or deprecate it. Then derive `basis_repr_tmul`, `basis_apply` and `basis_repr_symm_apply'` from `Basis.baseChange_repr_tmul` and `Basis.baseChange_apply`, or drop them. Delete `basisAux` and its two lemmas. State `toMatrix_baseChange`, `Basis.baseChange_linearMap` and `Basis.baseChange_end` with `b.baseChange A`. Keep `Algebra.TensorProduct.basis` as an abbreviation or deprecated alias only if the name is wanted. The reverse direction also works: make `Basis.baseChange` the thin wrapper over this construction, if that is preferred.

Benefit: There is one basis of the base change with one set of simp lemmas, so users no longer need to convert between `Algebra.TensorProduct.basis A b` and `b.baseChange A`. Simp sets are no longer split between two equal bases, and about 40 lines of duplicated construction and proof go away.

Source evidence:

- `Module.Basis.baseChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`: def baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=
  (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)
- `Module.Basis.baseChange_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`: b.baseChange S i = 1 ⊗ₜ b i
- `Module.Basis.baseChange_repr_tmul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`: (b.baseChange S).repr (x ⊗ₜ y) i = b.repr y i • x
- `use of Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/Trace.lean`: let b' := Algebra.TensorProduct.basis A b
- `use of Basis.baseChange_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/Kaehler/JacobiZariski.lean`: Basis.baseChange_apply

### concept-reinvention: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L109-L113)

Declaration: `Algebra.TensorProduct.instFree`

This instance is a second route to the same fact as Mathlib's `Module.Free.tensor`. `Module.Free.tensor` gives `Module.Free S (M ⊗[R] N)` from `Module.Free S M` and `Module.Free R N`. Taking `M := A` and `N := M` gives the same statement, because `Module.Free A A` is available as an instance. Instance resolution therefore has two ways to find the same class instance. This is the weakest part of the finding: the two are not literally the same declaration, and this one is proved from the competing basis.

Proposed change:

Either remove `instFree`, since `Module.Free.tensor` should already apply, or keep it and prove it with `Module.Free.of_basis (Module.Basis.baseChange A (Module.Free.chooseBasis R M))`. Check which instance is actually found before deleting. If it is kept, say in the docstring why it is kept.

Benefit: This avoids two competing instances and proofs of the same class, and removes the last dependence of the instance on the file's own basis construction.

Source evidence:

- `Module.Free.tensor` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Basis.lean`: instance Module.Free.tensor [Module.Free S M] [Module.Free R N] : Module.Free S (M ⊗[R] N) :=

### concept-reinvention: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L30-L51)

Declaration: `AddCircle.toCircle_addChar / ZMod.toCircle`

`PontryaginDuality.lean` builds the same circle-valued character of `ZMod n` by hand. `AddChar.zmod n x` rebuilds `AddCircle.toCircle` as an AddChar with an anonymous constructor and composes it with `ZMod.toAddCircle`. At `x = 1` this is `ZMod.toCircle`, and the two files never connect them. Each has its own formula lemma: `zmod_intCast` and `toCircle_intCast`. Each has its own injectivity proof: `zmod_injective` and `injective_toCircle`. A reader finds two unlinked versions of the standard character of `ZMod n` into `Circle`. The named `AddCircle.toCircle_addChar` is not reused where it applies.

Proposed change:

Reuse `AddCircle.toCircle_addChar` in `AddChar.zmod`, instead of the anonymous `⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩`. Add a bridging lemma showing `ZMod.toCircle = AddChar.zmod n 1`. If the import structure allows, define `AddChar.zmod n x` as `ZMod.toCircle.compAddMonoidHom (.mulLeft x)` and derive `zmod_intCast` and `zmod_injective` from the `ZMod.toCircle` lemmas. Otherwise, move `AddCircle.toCircle_addChar` to a lower-level file that both files import.

Benefit: There is one canonical `ZMod n → Circle` character, with the parametrised family defined from it. Formula and injectivity results are shared. Proofs in either file can be transferred without ad hoc unfolding.

Source evidence:

- `AddChar.zmod` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`: AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩ <|
    ZMod.toAddCircle.comp <| .mulLeft x
- `AddChar.zmod_intCast` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`: zmod n x y = exp (2 * π * (x * y / n))

### concept-reinvention: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L43-L50)

Declaration: `Finset.indicator' (with Finset.indicator'_apply and indicator'_injective)`

`Finset.indicator'` is a new definition of the indicator function `fun i => if i ∈ S then 1 else 0`. Mathlib already has this as `Set.indicator (↑S : Set U) (1 : U → ℝ)`. That definition comes with a large API: `Set.indicator_apply`, `Set.indicator_one_inj`, linearity and sum lemmas, and the `Finset.indicator_*` lemmas for finset sums. The new definition has no such API, so the file re-proves what Mathlib supplies. `indicator'_injective` is re-proved by hand with case analysis (lines 266–272), while `Set.indicator_one_inj` gives the same fact. The definition also sits in the root `Finset` namespace with a primed name. A prime marks a variant of an existing `Finset.indicator`-style concept, and it can clash with future Mathlib names.

Proposed change:

Drop the new definition. Use `Set.indicator (S : Set U) (1 : U → ℝ)` directly, or add `abbrev` / local notation in the `KaltonRoberts` namespace that unfolds to it. Then take injectivity from `Set.indicator_one_inj` plus `Finset.coe_injective`, and use `Set.indicator_apply` / `Finset.mem_coe` in place of `Finset.indicator'_apply`. The statements of `activeGenerators`, `clm_indicator'_eq_additiveFunction` and the other lemmas keep the same shape, with the indicator expression replaced.

Benefit: This removes a duplicate definition and its mini-API, and the root-namespace `Finset.indicator'` goes away. The lemmas then interoperate with Mathlib's indicator, sum and linear-map lemmas without conversion. Readers recognise the standard `Set.indicator` and need not check what `indicator'` means.

Source evidence:

- `Set.indicator (additive version of Set.mulIndicator)` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Notation/Indicator.lean`: `Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.
- `Set.indicator_one_inj` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/GroupWithZero/Indicator.lean`: lemma indicator_one_inj (h : indicator s (1 : ι → M₀) = indicator t 1) : s = t
- `indicator'_injective` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma indicator'_injective : Function.Injective (Finset.indicator' : Finset U → (U → ℝ))

### concept-reinvention: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L45-L49)

Declaration: `CKN.Leray.l2BasisVec (with private l2BasisVec_norm)`

L2Vec3 is `PiLp 2 (fun _ : Fin 3 => ℝ)`, which is definitionally `EuclideanSpace ℝ (Fin 3)`. `l2BasisVec i` is `WithLp.toLp 2 (Pi.single i 1)`, which is exactly Mathlib's `EuclideanSpace.single i 1` (`PiLp.single 2 i 1`). So this is a competing local definition of the standard basis vector. The private `l2BasisVec_norm` reproves `PiLp.norm_single`. Other parts of this repo (EllipticPDE) already use `EuclideanSpace.single i 1` or `PiLp.single`, so the two conventions coexist and the `PiLp.single` simp lemmas cannot be applied directly to `l2BasisVec`.

Proposed change:

Remove `l2BasisVec` and the private norm lemma, or make `l2BasisVec` a reducible abbreviation for `PiLp.single 2 i (1 : ℝ)` (or `EuclideanSpace.single i 1`). Use `PiLp.norm_single`, `PiLp.single_eq_same` and `PiLp.single_eq_of_ne` in `gradientOfCovectorLinear_norm_bound`, `inner_l2BasisVec` and the `l2Vec3Equiv (l2BasisVec i) = CKN.basisVec i` step of `weakTestGradientSchwartz_apply`. Keep a lemma linking `CKN.basisVec` to `Pi.single` only where needed.

Benefit: There is one standard basis-vector notion on L2Vec3. The `PiLp.single`/`EuclideanSpace.single` API (norm, apply, inner) becomes usable directly. Several local simp calls and the private norm lemma go away, and the code is consistent with the rest of the repo.

Source evidence:

- `EuclideanSpace.single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a
- `PiLp.norm_single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Normed/Lp/PiLp.lean`: lemma norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖
- `CKN.Foundation.Parabolic.L2Vec3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Basic.lean`: abbrev L2Vec3 := PiLp 2 (fun _ : Fin 3 => ℝ)

### concept-reinvention: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L35-L36)

Declaration: `CKN.Leray.l2Vec3Equiv`

This is a new definition whose body is Mathlib's `EuclideanSpace.equiv (Fin 3) ℝ`. That abbrev is `PiLp.continuousLinearEquiv 2 𝕜 _` on `EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜`. Here `L2Vec3` is `PiLp 2 (fun _ => ℝ)` (defeq to `EuclideanSpace ℝ (Fin 3)`) and `Vec3` is `Fin 3 → ℝ`, so the type is the same too. The new name hides the standard constant. It is used about 70 times across 5 files in this development, always with ad hoc unfolding via `simp [l2Vec3Equiv, ...]`.

Proposed change:

Replace the body by `EuclideanSpace.equiv (Fin 3) ℝ`, or make `l2Vec3Equiv` a `reducible` abbrev for it. Better, drop the definition and use `EuclideanSpace.equiv (Fin 3) ℝ` directly, with a short notation if the name is wanted. This lets Mathlib's simp/continuity lemmas about `EuclideanSpace.equiv` apply without unfolding.

Benefit: This avoids a parallel name for a standard Mathlib equivalence and lets library lemmas about `EuclideanSpace.equiv` apply directly. It also removes the need to unfold `l2Vec3Equiv` by hand in downstream simp calls.

Source evidence:

- `EuclideanSpace.equiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _
- `EuclideanSpace` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜

### concept-reinvention: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L35-L42)

Declaration: `LimitRepresentation.representationClosedCell (with representationClosedCell_compact)`

This declares a second copy of the closed unit cell `[0,1]^d` for `d = 2`, with the same doc comment and the same compactness proof. The library already has `FourierCalculus.closedCell d : Set (Vec d)` with `FourierCalculus.isCompact_closedCell d`. `FourierCalculus.continuous_integrableOn_closedCell` also already gives `IntegrableOn f (closedCell d)` for continuous `f`. The new definition adds nothing at `d = 2` except a different name, so the library now has two non-syntactically-equal names for one set. Lemmas about either one do not apply to the other without unfolding. The file re-proves compactness and re-does the continuous-on-compact integrability step instead of reusing the existing lemma.

Proposed change:

Delete `representationClosedCell` and `representationClosedCell_compact`. State `unitCube_subset_representationClosedCell` as `AVenhance.unitCube ⊆ FourierCalculus.closedCell 2`, or move it next to `closedCell` as a general-`d` lemma. In `smoothPeriodicTest_memL2On`, use `FourierCalculus.continuous_integrableOn_closedCell (hψ.continuous.pow 2)` and `.mono_set` with that subset lemma.

Benefit: There is a single canonical closed unit cell and a single compactness and integrability API. Future lemmas about the cell need not be proved twice or converted between two names, and about 8 lines of duplicated proof go away.

Source evidence:

- `FourierCalculus.closedCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/FourierCalculus.lean`: def FourierCalculus.closedCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
- `FourierCalculus.isCompact_closedCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/FourierCalculus.lean`: simpa [FourierCalculus.closedCell] using (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)
- `FourierCalculus.continuous_integrableOn_closedCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/FourierCalculus.lean`: (hf : Continuous f) : IntegrableOn f (FourierCalculus.closedCell d)

### concept-reinvention: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L45-L48)

Declaration: `planeCurveToBivariate`

This defines a second equivalence between `MvPolynomial (Fin 2) K` and `K[X][Y]`, next to Mathlib's `Polynomial.Bivariate.equivMvPolynomial`. The two differ only by the variable swap. The file itself proves this in `transposeBivariate_planeCurveToBivariate`, which states `transposeBivariate (planeCurveToBivariate K f) = (equivMvPolynomial K).symm f`. As a result the file carries parallel API for both orientations. There are three simp lemmas (`_X_zero`, `_X_one`, `_C`) and two degree lemmas: `planeCurveToBivariate_natDegree_eq_degreeOf_zero` and `bivariateEquiv_symm_natDegree_eq_degreeOf_one`. Several of these are reproved by `ringHom_ext` and `fin_cases` arguments. Neither the docstring nor the module docs justify keeping a separate equivalence rather than defining this one from the Mathlib one.

Proposed change:

Define `planeCurveToBivariate K` as `(Polynomial.Bivariate.equivMvPolynomial K).symm.trans Polynomial.Bivariate.swap`, or as `swap` composed with `equivMvPolynomial.symm`. Keep the name, and keep the orientation if the rest of the development needs it. Derive the `_X_zero`, `_X_one`, `_C` and natDegree lemmas from the Mathlib simp lemmas `equivMvPolynomial_symm_X_0`, `equivMvPolynomial_symm_X_1`, `equivMvPolynomial_symm_C`, `swap_X`, `swap_Y`, `swap_C_C`, and from the single degree lemma `bivariateEquiv_symm_natDegree_eq_degreeOf_one`. This removes the `finSuccEquiv` proofs and the bridging theorem `transposeBivariate_planeCurveToBivariate`.

Benefit: There would be one canonical bivariate presentation, with the oriented name kept as a thin wrapper. Readers would not have to convert between two presentations, and the duplicated generator, constant and degree proofs would shrink to reuse of Mathlib simp lemmas.

Source evidence:

- `Polynomial.Bivariate.equivMvPolynomial` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/Bivariate.lean`: def equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R :=
- `Polynomial.Bivariate.swap` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/Bivariate.lean`: def Bivariate.swap : R[X][Y] ≃ₐ[R] R[X][Y] :=
- `transposeBivariate_planeCurveToBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: transposeBivariate (planeCurveToBivariate K f) =
      (Polynomial.Bivariate.equivMvPolynomial K).symm f

### concept-reinvention: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L117-L126)

Declaration: `transposeBivariate_planeCurveToBivariate (use of the local transposeBivariate)`

The file leans on `transposeBivariate`, a local `RingHom` on `C[X][Y]` defined by `eval₂RingHom (mapRingHom C) (C X)`. It exchanges the two variables, which is exactly what Mathlib's `Polynomial.Bivariate.swap` does. `swap` is an `AlgEquiv` defined as `aevalAeval Y (C X)`. The local copy comes with its own API in BivariateResultant.lean: `transposeBivariate_C`, `transposeBivariate_X` and an involution lemma. Here it forces a hand-written `ringHom_ext` bridge to Mathlib's `equivMvPolynomial`, and it is used in the main theorem statements and proofs. Mathlib already has `swap_C`, `swap_X`, `swap_Y`, `swap_swap_apply` and `aevalAeval_swap`, but the local copy cannot use them. No comment explains why the Mathlib swap was not used.

Proposed change:

Redefine `transposeBivariate` as `Polynomial.Bivariate.swap.toRingEquiv.toRingHom`, or replace it by `Polynomial.Bivariate.swap` throughout. Prove its `_C`, `_X` and involution lemmas from `Bivariate.swap_C`, `swap_X` and `swap_swap_apply`. Then `transposeBivariate_planeCurveToBivariate` becomes a direct consequence of the definition of `planeCurveToBivariate` as `swap ∘ equivMvPolynomial.symm`.

Benefit: This removes a competing variable-exchange operation. It also lets downstream proofs reuse Mathlib's `swap` and `aevalAeval_swap` lemmas, and it cuts the conversions between the local and Mathlib presentations.

Source evidence:

- `transposeBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/BivariateResultant.lean`: Polynomial.eval₂RingHom
    (Polynomial.mapRingHom (Polynomial.C : C →+* Polynomial C))
    (Polynomial.C Polynomial.X)
- `Polynomial.Bivariate.swap_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/Bivariate.lean`: theorem Bivariate.swap_apply (p : R[X][Y]) : swap p = p.aevalAeval (A := R[X][Y]) Y (C X) := rfl
