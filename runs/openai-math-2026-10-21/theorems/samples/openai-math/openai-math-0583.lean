namespace OAI

noncomputable section

namespace Generator.Tracial

section

open scoped BigOperators

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_small_energy_piece {I J : Type*} (s : Finset I) (F : Finset J)
    (t : I → ℝ) (a : I → J → ℝ) (ε : ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (ha : ∀ i ∈ s, ∀ j ∈ F, 0 ≤ a i j)
    (h : ∑ i ∈ s, ∑ j ∈ F, a i j < ε * ∑ i ∈ s, t i) :
    ∃ i ∈ s, 0 < t i ∧ ∀ j ∈ F, a i j < ε*t i := by
  classical
  have hex : ∃ i ∈ s, (∑ j ∈ F, a i j) < ε*t i := by
    by_contra hn
    push Not at hn
    have he := Finset.sum_le_sum hn
    rw [← Finset.mul_sum] at he
    exact (not_lt_of_ge he) h
  obtain ⟨i,hi,he⟩ := hex
  have htpos : 0 < t i := by
    by_contra hn
    have hz : t i=0 := le_antisymm (le_of_not_gt hn) (ht i hi)
    rw [hz,mul_zero] at he
    exact (not_lt_of_ge (Finset.sum_nonneg (ha i hi))) he
  refine ⟨i,hi,htpos,fun j hj => ?_⟩
  exact (Finset.single_le_sum (ha i hi) hj).trans_lt he

end
end Generator.Tracial
end
end OAI
