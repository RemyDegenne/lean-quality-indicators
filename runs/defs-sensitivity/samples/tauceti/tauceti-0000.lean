public section

open MeasureTheory Set

namespace TauCeti

/-- A set is Lipschitz parametrizable in dimension `d` if it is covered by finitely many
Lipschitz images of the unit cube in `Fin d → ℝ`. -/
def IsLipschitzParametrizable {E : Type*} [PseudoEMetricSpace E] (d : ℕ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
    (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
      S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1

end TauCeti
end
