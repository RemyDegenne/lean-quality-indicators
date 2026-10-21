namespace OAI

noncomputable section

open scoped TensorProduct ENNReal ComplexOrder

open UniformSpace

open CStarAlgebra

open scoped NNReal

open scoped TensorProduct ComplexConjugate

open scoped ENNReal InnerProductSpace

open scoped InnerProductSpace

open scoped TensorProduct InnerProductSpace

open Filter Topology

open Complex selfAdjoint

open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder B] [StarOrderedRing B] in
lemma separation_second_coverage_identity (b X : B) {l : ℝ} (hl : 0 < l) :
    (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=b*cfc (separationN l) (star X*X) := by
  have he : (b*cfc (separationR l) (star X*X))*cfc (separationN l) (star X*X)*
      cfc (separationJ l) (star X*X)=
      b*(cfc (separationR l) (star X*X)*cfc (separationN l) (star X*X)*cfc (separationJ l) (star X*X)) := by
    simp only [mul_assoc]
  rw [he,cfc_real_mul_three _ (IsSelfAdjoint.star_mul_self X) _ _ _
    (continuous_separationR hl) (continuous_separationN l) (continuous_separationJ l)]
  congr 1
  apply cfc_congr
  intro s _
  calc
    _=(separationR l s*separationJ l s)*separationN l s := by ring
    _=_ := by rw [separationRJ hl,one_mul]

end
end
end WeakPureInfiniteness
end
end OAI
