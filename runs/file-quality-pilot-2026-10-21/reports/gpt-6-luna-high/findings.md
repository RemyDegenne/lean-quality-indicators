# Findings

### statement-generality: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L109-L113)

Declaration: `Algebra.TensorProduct.instFree`

The instance requires A to be commutative, although the basis used to prove freeness only requires A to be a semiring. This excludes base changes to noncommutative algebras despite the same proof applying.

Proposed change:

Replace `[CommSemiring A]` with `[Semiring A]` in the instance assumptions, retaining `[Algebra R A]`. The existing proof via `Module.Free.of_basis` applied to `Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)` works with those assumptions.

Benefit: Makes the freeness result available for base change to noncommutative semirings, without changing the result for commutative A. The empty-basis case is unchanged: the construction still supplies a basis when M is zero.

Source evidence:

- `Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: variable [CommSemiring R] [Semiring A] [Algebra R A]
- `Module.Free.of_basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/FreeModule/Basic.lean`: variable [Semiring R] [AddCommMonoid M] [Module R M]

### statement-generality: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L53-L75)

Declaration: `clm_decompose and clm_indicator'_eq_additiveFunction`

Both helper statements require a continuous linear map, but their proofs only use linearity (`map_smul` and `map_sum`) to evaluate finite sums. Continuity is not needed for these identities, so the statements are unnecessarily specialized.

Proposed change:

Change the argument in both declarations at lines 53–54 and 71–72 from `(Λ : (U → ℝ) →L[ℝ] ℝ)` to `(Λ : (U → ℝ) →ₗ[ℝ] ℝ)`. Their existing proofs use linear-map operations. At the later calls where the separating functional is a continuous linear map, pass `Λ.toLinearMap` if elaboration does not insert the coercion.

Benefit: The identities become reusable for any linear functional, including where no topology or continuity structure is available. This preserves the finite-sum mathematics and does not change the Hahn–Banach argument, which still uses a continuous linear map.

Source evidence:

- `clm_decompose` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: rw [this, map_smul, smul_eq_mul]
- `clm_decompose` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: _ = ∑ i, Λ (Function.update (0 : U → ℝ) i (h i)) := map_sum Λ _ _
- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L95-L99)

Declaration: `fourier_postcompCLM`

The theorem is generic in its value spaces and postcomposition map, but fixes the Fourier domain to `L2Vec3`. Mathlib’s Schwartz Fourier API is stated for any finite-dimensional real inner-product domain, so this useful postcomposition identity is unnecessarily restricted to the library’s 3D coordinates.

Proposed change:

Replace the fixed domain with a variable `V` carrying `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]`, and change `SchwartzMap L2Vec3 F` to `SchwartzMap V F`. The proof can use the same `Real.fourier_eq` rewrites and `L.integral_comp_comm` argument. This formulation includes the zero-dimensional case; no nonzero-dimension assumption is needed for the integral-commutation argument.

Benefit: The identity becomes reusable for Schwartz Fourier transforms on other finite-dimensional real inner-product spaces, without duplicating its proof for each spatial domain.

Source evidence:

- `fourier_postcompCLM` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: (L : F →L[ℂ] G) (f : SchwartzMap L2Vec3 F) :
- `SchwartzMap Fourier variables` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`: {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

### statement-generality: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L154-L159)

Declaration: `sectorCurve_norm_on_arc`

The arc’s modulus is stated as `r` only under the positivity assumption. For any real `r`, including zero and negative values, its modulus is `|r|`; the arc formula itself does not require positivity.

Proposed change:

State `theorem sectorCurve_norm_on_arc (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) : ‖sectorCurve r α t‖ = |r|`. The proof can rewrite with `sectorCurve_seg2` and use the norm of a product and `Complex.norm_exp_I_mul_ofReal`; the real scalar factor contributes `|r|`.

Benefit: This gives the actual modulus formula without restricting the radius parameter to positive reals, including the degenerate case `r = 0`, and makes the geometric fact usable for signed parameters.

Source evidence:

- `sectorCurve_norm_on_arc` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (le_of_lt hr)

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L387-L393)

Declaration: `parabolicRieszKernel_tail_le (with matching weakening in its helper lemmas)`

The estimate is restricted to q ≥ 1, although the Morrey cell and norm are defined for real q, and the inspected proof uses this lower bound only to obtain q > 0 (and, in the scale identity, to establish an unused nonnegativity fact). The estimates therefore need not exclude positive q below 1.

Proposed change:

Replace the q hypothesis with `hq : 0 < q` in `parabolicRieszKernel_tail_le` and the corresponding helper signatures (`cylinderAbsIntegral_le_morreyNorm`, `positive_shell_integral_le`, and `positive_shell_scale_identity`). In the scale-identity proof, use hq directly for q positivity and remove or replace the auxiliary `hα` proof, which is not used later. The cylinder integral estimate still follows from the Morrey supremum bound and cancellation of the radius powers; the shell estimate uses that cylinder estimate, while `ennreal_mul_rpow` already handles either sign of its exponent. The dyadic decay condition `β * q < 5` remains in place.

Benefit: This admits the same tail bound for positive q < 1, extending its use to quasi-Morrey parameters without changing the geometry or the stated estimate. The positive-q condition also preserves the meaningful division by q; no q = 0 case is introduced.

Source evidence:

- `parabolicRieszKernel_tail_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: (hq : 1 ≤ q) (hβq : β * q < 5)
- `cylinderAbsIntegral_le_morreyNorm` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: (hq : 1 ≤ q)
- `positive_shell_scale_identity` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: have hα : 0 ≤ α := by
- `morreyNorm` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Basic.lean`: def morreyNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=

### simp-interface: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L88-L89)

Declaration: `DFinsupp.mem_singleton_apply_iff`

The theorem gives the expected normal form for membership in the pointwise singleton, but is not tagged `[simp]`. Thus the direct expression `a ∈ f.singleton i` does not have this rule available to `simp`, even though the underlying Finset membership rule is a simp lemma.

Proposed change:

Add `@[simp]` to `mem_singleton_apply_iff`, so `simp` rewrites `a ∈ f.singleton i` to `a = f i`.

Benefit: Users can discharge or normalize membership goals involving the bundled singleton with the standard simplifier, consistently with `Finset.mem_singleton`.

Source evidence:

- `DFinsupp.mem_singleton_apply_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton
- `Finset.mem_singleton` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/Finset/Insert.lean`: @[simp, grind =]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=

### simp-interface: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L71-L75)

Declaration: `clm_indicator'_eq_additiveFunction`

This useful normalization is not in the simp set. The file has to invoke it manually when reasoning about a continuous linear map applied to an indicator: it constructs the equality with `convert` at lines 155–156 and rewrites with the lemma at lines 162–163. Thus ordinary `simp` does not normalize `Λ S.indicator'` to the additive function of the basis evaluations.

Proposed change:

Add `@[simp]` to `clm_indicator'_eq_additiveFunction`, keeping its current orientation. The desired normal form is `additiveFunction (fun i => Λ (Function.update 0 i 1)) S` for `Λ S.indicator'`. This rewrite removes the indicator application rather than recreating it, so it does not introduce an evident rewrite cycle. It also applies in the empty-finset case, where the additive function is the empty sum.

Benefit: Users can simplify linear-map applications to indicators directly and avoid repeated explicit `convert`/`rw` steps, as already needed in this proof.

Source evidence:

- `clm_indicator'_eq_additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma clm_indicator'_eq_additiveFunction (Λ : (U → ℝ) →L[ℝ] ℝ) (S : Finset U) :
    Λ S.indicator' = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have hΛ_S : Λ (S.indicator') = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
      convert clm_indicator'_eq_additiveFunction Λ S using 1;
- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have h_additiveFunction_a_neg : additiveFunction a S = -Λ (S.indicator') := by
      rw [ clm_indicator'_eq_additiveFunction Λ S ]; ring_nf!;

### simp-interface: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L147-L150)

Declaration: `weakTestGradientSchwartz_apply`

This establishes a useful canonical component normal form for the exposed `weakTestGradientSchwartz` definition, but the theorem is private and is not tagged `[simp]`. Consequently downstream users cannot use this normal form to simplify component expressions; unfolding the definition instead exposes the derivative, postcomposition, and coordinate-equivalence implementation. The file itself uses the equation in a componentwise proof.

Proposed change:

Make this equation public and tag it `[simp]`, preserving the stated orientation: `weakTestGradientSchwartz ψ x i` simplifies to `(ψ.partialDeriv i (l2Vec3Equiv x) : ℂ)`.

Benefit: Users of the exposed gradient encoding can obtain the coordinate derivative as a stable, concise normal form without unfolding its construction. The rule reduces an application to the mathematical quantity it represents and does not expand that quantity back into the implementation.

Source evidence:

- `weakTestGradientSchwartz` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: def weakTestGradientSchwartz
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    SchwartzMap L2Vec3 ComplexVec3 :=
- `realPart_isWeakDivFree_of_fourierOrthogonal` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: weakTestGradientSchwartz_apply,
      RCLike.inner_apply

### simp-interface: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L74-L83)

Declaration: `sectorCurve_zero and sectorCurve_three`

These canonical endpoint evaluations are not simp lemmas. A downstream proof must name both explicitly to simplify the endpoint values, even though their right-hand sides are terminal values and rewriting them cannot expand the curve or create a rewrite cycle.

Proposed change:

Add `@[simp]` to `sectorCurve_zero` and `sectorCurve_three` so ordinary `simp` calls normalize these endpoint evaluations.

Benefit: Downstream endpoint calculations can use the standard simplifier instead of repeatedly listing these theorems, while preserving the endpoint values and behavior at degenerate parameter choices.

Source evidence:

- `sectorCurve_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by simp [sectorCurve]
- `sectorCurve_three` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
- `pv_sector_higher_power` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),

### readable-proof-simplification: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L60-L61)

Declaration: `CategoryTheory.Functor.IsWellOrderContinuous instance for ℕ`

The proof relies on `simp` to discover that `hm` is impossible, leaving the reason this instance is vacuous implicit. The adjacent Fin instance uses a named order-theory result for the same fact.

Proposed change:

Replace the proof with `nonempty_isColimit m hm := (Order.not_isSuccLimit_of_isSuccArchimedean hm).elim`.

Benefit: The named lemma makes the key mathematical reason explicit: an Archimedean successor order has no successor-limit elements. This is at least as easy to follow as asking `simp` to close the goal, and aligns the ℕ proof with the neighboring Fin proof.

Source evidence:

- `CategoryTheory.Functor.IsWellOrderContinuous instance for ℕ` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean`: nonempty_isColimit m hm := by simp at hm
- `CategoryTheory.Functor.IsWellOrderContinuous instance for Fin n` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean`: nonempty_isColimit _ hj := (Order.not_isSuccLimit_of_isSuccArchimedean hj).elim
- `Order.not_isSuccLimit_of_isSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Limit.lean`: theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
- `Nat.instSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Nat.lean`: instance : IsSuccArchimedean ℕ :=

### readable-proof-simplification: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L167-L174)

Declaration: `continuousOn_schwarzChristoffelBoundary`

This proof obtains a local continuous extension and then identifies it pointwise with the canonical boundary map. The earlier theorem `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one` already gives continuity of that canonical map on any set where the exponent sum is greater than `-1`, and the preceding sum lemma establishes that condition on this interval.

Proposed change:

Replace the proof with:
```lean
  apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
  intro x hx
  rw [sum_filter_eq_zero_of_mem_Ioo a e ha hx]
  norm_num
```

Benefit: This reuses the theorem whose conclusion is exactly the desired continuity and avoids constructing and identifying a second extension. The short proof makes the mathematical reason explicit: the exponent sum vanishes throughout the prevertex-free interval, so it is greater than `-1`.

Source evidence:

- `continuousOn_schwarzChristoffelBoundary` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:   obtain ⟨L, hL, hLcont, -⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
- `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:     ContinuousOn (schwarzChristoffelBoundary a e z₀) s := by
- `sum_filter_eq_zero_of_mem_Ioo` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:     ∑ i with a i = x, e i = 0 := by

### readable-proof-simplification: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L92-L98)

Declaration: `IsSl2System.structureConstant_mul_structureConstant_neg_neg`

The two hypotheses prove the same root-sum equality in opposite summand orders by repeating the coercion rewrite and abelian normalization. The second equality follows directly from the first by commutativity.

Proposed change:

Replace the `hγα` proof with `have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) := hβγ.trans (by rw [add_comm])`.

Benefit: This reuses the already-established root relation and makes explicit that the cyclic-symmetry input differs only by the order of its summands. The short `add_comm` step remains easy to interpret, while avoiding a second normalization proof.

Source evidence:

- `IsSl2System.structureConstant_mul_structureConstant_neg_neg` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean`: have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, hαβ]
    abel
- `ModEq.modEq_sub_iff_add_modEq'` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Group/ModEq.lean`: modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L153-L158)

Declaration: `zero_mem_convexHull_of_best_approx`

This uses broad `simp_all` and a separate `convert` to relate the indicator to its additive-function sum, obscuring the short argument: the chosen additive function sums to the negative of Λ applied to the indicator, which is positive by `hΛ_gen`.

Proposed change:

Replace the proof of `h_additiveFunction_a_pos` with:
```lean
  have h_additiveFunction_a_pos : ∀ S : Finset U, f S = M → additiveFunction a S > 0 := by
    intro S hS
    have hΛ_S := clm_indicator'_eq_additiveFunction Λ S
    simp only [ha_def, additiveFunction, Finset.sum_neg_distrib]
    rw [← hΛ_S]
    exact neg_pos.mpr (hΛ_gen S hS)
```

Benefit: The proof directly exposes the sign reversal that drives the argument and uses the existing indicator-sum identity, rather than relying on broad simplification and a final arithmetic tactic.

Source evidence:

- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`:     have hΛ_S : Λ (S.indicator') = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
      convert clm_indicator'_eq_additiveFunction Λ S using 1;
    simp_all +decide [ additiveFunction ];
    linarith [ hΛ_gen S hS ];
- `clm_indicator'_eq_additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma clm_indicator'_eq_additiveFunction (Λ : (U → ℝ) →L[ℝ] ℝ) (S : Finset U) :
    Λ S.indicator' = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by

### readable-proof-simplification: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288-L290)

Declaration: `log_cancellation`

This reproves the first-segment logarithmic integral even though the file has already established that formula in `integral_seg1_eq_neg_log`.

Proposed change:

Replace the proof of `h1` with `exact integral_seg1_eq_neg_log (ε / r) hεr_pos hεr_lt1`.

Benefit: Reusing the named segment result removes the integral and logarithm rewrite sequence while making the first-segment contribution explicit and easy to recognize.

Source evidence:

- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L422-L431)

Declaration: `parabolicRieszKernel_tail_le`

The function equality `hfun` is reflexivity: the additional parentheses in its right-hand function do not change the expression. Establishing it by function extensionality adds an unnecessary intermediate step.

Proposed change:

Replace lines 422–431 with:
```lean
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      rfl
```

Benefit: This removes a vacuous function-extensionality proof while keeping the argument clear: the two tsum rewrites factor out `T` and `N`, leaving the definition of `parabolicTailKernelConstant`.

Source evidence:

- `ENNReal.tsum_mul_right` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`: protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293)

Declaration: `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow and Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

Both declarations repeat the same asymptotic reasoning: multiply the two Big-O bounds, use that the base is eventually at least 1 to combine powers, then use monotonicity in the exponent to compare with the target power. The natural-number proof differs only in converting its eventual bound to a real inequality.

Proposed change:

Introduce a shared lemma for an arbitrary `u : α → ℝ` with `1 ≤ᶠ[l] u`: if `f =O[l] fun x => u x ^ a`, `g =O[l] fun x => u x ^ b`, and `a + b ≤ c`, then `f * g =O[l] fun x => u x ^ c`. Prove it once by multiplying the bounds, combining powers using `Real.rpow_add` on the eventual positivity supplied by `u ≥ 1`, and applying exponent monotonicity. Rewrite the real-parameter theorem using `u := id` and `eventually_ge_atTop 1`; rewrite the natural-parameter theorem using `u := fun n => (n : ℝ)` and `Nat.one_le_cast.mpr` to establish the helper's eventual hypothesis. This generalizes the shared result rather than merely relocating a duplicated branch.

Benefit: Readers can find and reuse the underlying product-of-power-bounds result independently of whether the parameter is real or natural. Maintaining the eventual-base and exponent-comparison argument in one proof also prevents the two public results from drifting.

Source evidence:

- `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`:   refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h
- `Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`:   refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358-L363)

Declaration: `Pattern across `pv_cutoff_F_integrable_delta_1` and `pv_cutoff_integral_seg1_eq_inv``

These proofs independently establish the same substantive cutoff fact: on the truncated first ray, the cutoff is active because the curve norm exceeds ε, and the integrand is 1/t. Both re-derive the threshold inequality using δ = ε/r and invoke the segment norm and integrand formulas. Keeping the identity in one lemma would avoid drift between the integrability and integral-replacement arguments.

Proposed change:

Introduce a shared private lemma, under `hr : 0 < r`, `hε : 0 < ε`, and `hεr : ε < r`, stating that for the cutoff function F and `δ := ε / r`, every `t ∈ Ioo δ 1` satisfies `F t = (↑(t⁻¹) : ℂ)`. Prove it once using `sectorCurve_norm_seg1` to show the cutoff is active and `pv_integrand_seg1` to identify the value. In `pv_cutoff_F_integrable_delta_1` (lines 358–363) and `pv_cutoff_integral_seg1_eq_inv` (lines 504–513), replace the local `h_eq` proofs with this shared result under their existing hypotheses; each consumer can retain its current integrability or almost-everywhere integral argument.

Benefit: Centralizes the geometric cutoff threshold and integrand calculation, so the two arguments use the same verified identity and are easier to maintain. This uses existing declarations and imports; no additional imports are needed.

Source evidence:

- `pv_cutoff_F_integrable_delta_1` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_eq : ∀ t ∈ Ioo δ (1 : ℝ), F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]
    · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith
- `pv_cutoff_integral_seg1_eq_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]
    · rw [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩,
          deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ htδ, ht1⟩]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans hδ htδ))
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      push_cast; field_simp
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith
