namespace OAI

attribute [-instance] CategoryTheory.Sigma.sigma

attribute [instance] PosetAttachment.order

attribute [-instance] CategoryTheory.Sigma.sigma

noncomputable section

universe u v w z

namespace Thomason.GlobeComplex

open CategoryTheory DirectedComplex DirectedComplex.Table

@[simp] lemma faceMap_self (n : ℕ) (b : Bool) :
    faceMap.{u} n n b = Hom.id (complex n) := by
  apply hom_ext
  rw [faceMap_top]
  change truncate n b (topTable n) = topTable n
  rw [← face_nu]
  exact (complex n).nu.face_of_fixed (topTable_bounded n) (le_refl n) b

end Thomason.GlobeComplex
end
end OAI
