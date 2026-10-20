@[expose] public section

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

lemma triangEnvelopeIter_add [IsTriangulated C] {n m n' : ℕ} (h : n = n' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n') (P.triangEnvelopeIter m)).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]

end CategoryTheory.ObjectProperty
end
