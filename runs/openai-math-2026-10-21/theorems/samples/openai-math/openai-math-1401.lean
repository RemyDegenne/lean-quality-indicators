namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable

noncomputable section

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.SignedTensor.ExceptionPattern

open PositiveTensor

variable {p l : ℕ}

lemma component_inclusion (F : ExceptionPattern p l) (A : commutant p l) :
    F.component A = (inclusion F.embedding).mulVec (fun x => A.val (F.fill x).1 (F.fill x).2) := by
  funext q
  by_cases hq : q ∈ Set.range F.fill
  · obtain ⟨x,rfl⟩ := hq
    have hh := inclusion_mulVec_image F.embedding (fun x => A.val (F.fill x).1 (F.fill x).2) x
    change (inclusion F.embedding).mulVec (fun x => A.val (F.fill x).1 (F.fill x).2) (F.fill x) = _ at hh
    exact (F.component_image A x).trans hh.symm
  · rw [show F.component A q = 0 from ite_eq_right hq]
    exact (inclusion_mulVec_notin F.embedding _ q hq).symm

end CoordinateSweeps.SignedTensor.ExceptionPattern
end
end
end
end OAI
