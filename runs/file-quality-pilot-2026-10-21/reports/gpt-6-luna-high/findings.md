# Findings

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
