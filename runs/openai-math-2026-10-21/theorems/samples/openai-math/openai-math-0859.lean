namespace OAI

namespace Ostmann

open Complex

theorem characterGamma_logarithmic_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤
        B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := gammaReal_logarithmic_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann
end OAI
