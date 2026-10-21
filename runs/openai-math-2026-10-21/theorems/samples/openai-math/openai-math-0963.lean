namespace OAI

noncomputable section

open scoped BigOperators

namespace ContinuumCoulomb

theorem exists_uniform_counterterm_scale {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ E : ℕ, 0 < E ∧ ∀ N : ℝ, 2 ≤ N → ∀ (m : ℕ), (m : ℝ) ≤ N ^ A →
      ∀ (u : Fin m → PlanarPosition) (i : Fin m),
        0 ≤ localizedCounterterm freq u i / N ^ E ∧ localizedCounterterm freq u i / N ^ E ≤ 1 / 2 := by
  obtain ⟨L, hL, hbound⟩ := exists_polynomial_constant_bounds (by norm_num : (0 : ℝ) < 1)
    (localizedCountertermBound freq)
  refine ⟨A + L + 1, by omega, fun N hN m hm u i => ?_⟩
  have hNp : 0 < N := by linarith
  have hb : localizedCounterterm freq u i ≤ N ^ (A + L) := by
    calc
      _ ≤ m * localizedCountertermBound freq := localizedCounterterm_bound hfreq u i
      _ ≤ N ^ A * N ^ L := mul_le_mul hm (hbound N hN).2
        (localizedCountertermBound_nonnegative freq) (pow_nonneg hNp.le A)
      _ = _ := (pow_add _ _ _).symm
  refine ⟨div_nonneg (localizedCounterterm_nonnegative freq u i) (pow_pos hNp _).le, ?_⟩
  apply (div_le_iff₀ (pow_pos hNp _)).mpr
  rw [pow_succ]
  have h := mul_le_mul_of_nonneg_left hN (pow_nonneg hNp.le (A + L))
  nlinarith only [hb, h]

end ContinuumCoulomb
end
end OAI
