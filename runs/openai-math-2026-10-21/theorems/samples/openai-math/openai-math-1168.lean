namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedFiniteNestedResourceLayerSourceExponent_bounds
    (m q cutoff e Cprimitive Cdirect extra A : ℕ)
    (hA : preparedFiniteNestedResourceLayerSourceExponent
      m q cutoff e Cprimitive Cdirect extra ≤ A) :
    2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A ∧
    ∀ d ≤ cutoff, allocatedCandidateForwardScheduleExponent d m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ A := by
  have hfields : 2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A := by
    unfold preparedFiniteNestedResourceLayerSourceExponent at hA
    omega
  refine ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2, ?_⟩
  intro d hd
  have hsum := Finset.single_le_sum
    (f := fun i : Fin (cutoff + 1) => allocatedCandidateForwardScheduleExponent i.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ _ at hsum
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ A
  unfold preparedFiniteNestedResourceLayerSourceExponent at hA
  omega

end Erdos3.VectorPolynomial
end
end OAI
