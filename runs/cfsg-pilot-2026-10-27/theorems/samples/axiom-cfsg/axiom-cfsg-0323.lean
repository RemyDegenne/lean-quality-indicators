public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_list_of_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ lipschitzGroup Q) :
    ∃ l : List V, (∀ a ∈ l, Q a ≠ 0) ∧ (x : CliffordAlgebra Q) = (l.map (ι Q)).prod := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hx
    refine ⟨[m], ?_, by simp [hm]⟩
    simp only [List.mem_singleton, forall_eq]
    exact (isUnit_of_isUnit_ι' Q (hm ▸ x.isUnit)).ne_zero
  | inv_mem x hx =>
    obtain ⟨m, hm⟩ := hx
    have hQm : Q m ≠ 0 := (isUnit_of_isUnit_ι' Q (hm ▸ x.isUnit)).ne_zero
    refine ⟨[(Q m)⁻¹ • m], ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      rw [QuadraticMap.map_smul, smul_eq_mul]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hQm) (inv_ne_zero hQm)) hQm
    · rw [List.map_singleton, List.prod_singleton]
      refine Units.inv_eq_of_mul_eq_one_left ?_
      rw [← hm, map_smul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ hQm, map_one]
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, hl₁, hx⟩ := hx
    obtain ⟨l₂, hl₂, hy⟩ := hy
    refine ⟨l₁ ++ l₂, fun a ha => ?_, by
      rw [Units.val_mul, hx, hy, List.map_append, List.prod_append]⟩
    rcases List.mem_append.mp ha with ha | ha
    exacts [hl₁ a ha, hl₂ a ha]

end CFSG.LieType.Universal.Spin
end
