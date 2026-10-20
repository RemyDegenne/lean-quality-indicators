@[expose] public section

open scoped BigOperators

namespace EGZ

namespace CommonMeasure

variable {α : Type*} [Fintype α]

open WeightedIncidence

theorem final_mass_le (w u : α → ℝ) (hu : ∀ a, 0 ≤ u a)
    (hle : ∀ a, u a ≤ w a) {ε R : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R)
    (hloss : (∑ a, (w a - u a)) ≤ ε ^ 2 / 4 * R)
    (S P Q : Set α) (hlarge : ε * R ≤ mass w S)
    (hSQ : S ⊆ Q) (hP : mass w P ≤ R) :
    ε / 2 * mass u P ≤ mass u Q :=
  (relative_mass_le w u hle hε hεhalf hR hloss S P hlarge hP).trans
    (mass_mono u hu hSQ)

end CommonMeasure
end EGZ
end
