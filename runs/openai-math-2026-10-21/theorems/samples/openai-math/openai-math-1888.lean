namespace OAI

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G : Type*} [Group G] [MeasurableSpace G]

theorem switchParameterLaw_success_finite [MeasurableMul₂ G] [MeasurableInv G]
    (σ : ℕ → Measure G) [∀ j, IsProbabilityMeasure (σ j)]
    (S : ℕ → Set G) (n k : ℕ)
    (hS : ∀ j, n < j → j ≤ n + k → MeasurableSet (S j)) (x : G) :
    MeasurableSet {p : SwitchParameters G k | SwitchSuccessful S n k x p} ∧
      switchParameterLaw σ n k {p | SwitchSuccessful S n k x p} =
        survivingSwitchProbability σ S n k x := by
  let R := fun j => if n < j ∧ j ≤ n + k then S j else ∅
  have hR (j : ℕ) : MeasurableSet (R j) := by
    by_cases hj : n < j ∧ j ≤ n + k
    · simpa [R, hj] using hS j hj.1 hj.2
    · simp [R, hj]
  have heq (j : ℕ) (hj : n < j) (hj' : j ≤ n + k) : S j = R j := by
    simp [R, hj, hj']
  have hsets : {p : SwitchParameters G k | SwitchSuccessful S n k x p} =
      {p | SwitchSuccessful R n k x p} := by
    ext p
    exact switchSuccessful_congr S R n k heq x p
  constructor
  · exact hsets.symm ▸ measurableSet_switchSuccessful_fixed R hR n k x
  · calc
      _ = switchParameterLaw σ n k {p | SwitchSuccessful R n k x p} :=
        congrArg (switchParameterLaw σ n k) hsets
      _ = survivingSwitchProbability σ R n k x := switchParameterLaw_success σ R hR n k x
      _ = _ := (survivingSwitchProbability_congr σ S R n k heq x).symm

end PolycyclicRecognition
end
end OAI
