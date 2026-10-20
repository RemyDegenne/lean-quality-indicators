@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_mathlib_exposedPoint_inner_lt_of_isCompact_of_inner_lt
    {s : Set E} (hcompact : IsCompact s) {normal x : E} {u : ℝ}
    (hx : x ∈ s)
    (hgap : u < inner ℝ normal x) :
    ∃ p : E, p ∈ Set.exposedPoints ℝ s ∧ u < inner ℝ normal p := by
  have hcont : ContinuousOn (fun z : E => ‖z - x‖ ^ 2) s := by
    fun_prop
  obtain ⟨r, hr, hrmax⟩ := hcompact.exists_isMaxOn ⟨x, hx⟩ hcont
  let M : ℝ := ‖r - x‖ ^ 2
  let gap : ℝ := inner ℝ normal x - u
  let lam : ℝ := (M + 1) / (2 * gap)
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hgap
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hlam : 0 < lam := by
    dsimp [lam]
    exact div_pos (by nlinarith) (by nlinarith)
  have hscale : 2 * lam * (inner ℝ normal x - u) = M + 1 := by
    have hgap_ne : inner ℝ normal x - u ≠ 0 := (sub_pos.mpr hgap).ne'
    dsimp [lam, gap]
    field_simp [hgap_ne]
  have hbound :
      ∀ ⦃z : E⦄, z ∈ s → ‖z - x‖ ^ 2 < 2 * lam * (inner ℝ normal x - u) := by
    intro z hz
    have hzle : ‖z - x‖ ^ 2 ≤ M := by
      simpa [M] using (isMaxOn_iff.mp hrmax) z hz
    nlinarith
  obtain ⟨p, _hp, hexposed, hpout⟩ :=
    exists_exposesPoint_and_inner_lt_of_forall_norm_sub_sq_lt
      (s := s) hcompact (normal := normal) (x := x) (u := u) (lam := lam)
      hx hlam hbound
  exact ⟨p, hexposed.mem_mathlib_exposedPoints, hpout⟩

end AleksandrovDifferentiability
end
