namespace OAI

section

noncomputable section

open Matrix

open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem path_succ_position (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (k : ℕ) (hk : k < 5) :
    (path σ s α γ z q (k+1)).2.1 = (path σ s α γ z q k).2.1-
      ((path σ s α γ z q k).1-q.1 ⟨k,hk⟩) • (path σ s α γ z q k).2.2 := by
  simp only [path,dite_eq_left hk,step]

end BoltzmannNonuniqueness.FiveGainMap
end
end
end OAI
