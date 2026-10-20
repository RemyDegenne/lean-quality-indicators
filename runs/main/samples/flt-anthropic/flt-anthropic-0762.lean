namespace P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

p2m_open

namespace VbUnrq

section Generation

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  (φ : F →ₐ[K] F')

theorem exists_common_denom (W : Place K F') (T : Finset F) :
    ∃ d : F, d ≠ 0 ∧ φ d ∈ W.toValuationSubring ∧ ∀ t ∈ T, φ (d * t) ∈ W.toValuationSubring := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by rw [map_one]; exact one_mem _, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert t T htT ih =>
    obtain ⟨d, hd0, hd, hT⟩ := ih
    by_cases ht : φ (d * t) ∈ W.toValuationSubring
    · refine ⟨d, hd0, hd, fun s hs => ?_⟩
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact ht
      · exact hT s hs
    · have ht0 : d * t ≠ 0 := by
        intro h0; apply ht; rw [h0, map_zero]; exact zero_mem _
      have hinv : φ (d * t)⁻¹ ∈ W.toValuationSubring := by
        rcases W.toValuationSubring.mem_or_inv_mem (φ (d * t)) with h1 | h1
        · exact absurd h1 ht
        · rwa [← map_inv₀] at h1
      refine ⟨d * (d * t)⁻¹, mul_ne_zero hd0 (inv_ne_zero ht0), ?_, fun s hs => ?_⟩
      · rw [map_mul]; exact mul_mem hd hinv
      rcases Finset.mem_insert.mp hs with rfl | hs
      · have hs0 : s ≠ 0 := right_ne_zero_of_mul ht0
        have : d * (d * s)⁻¹ * s = 1 := by field_simp
        rw [this, map_one]; exact one_mem _
      · have : d * (d * t)⁻¹ * s = (d * s) * (d * t)⁻¹ := by ring
        rw [this, map_mul]; exact mul_mem (hT s hs) hinv

end Generation
end VbUnrq
end P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst
