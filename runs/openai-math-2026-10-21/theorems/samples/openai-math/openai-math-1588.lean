namespace OAI

noncomputable section

open Filter Topology MeasureTheory

open scoped BigOperators ComplexOrder InnerProductSpace ComplexStarModule CStarAlgebra

namespace BoundedHochschild

open HochschildNormalPart

universe u v

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma normalAt_pairSlice {n : ℕ} (f : Cochain M (n+2)) (r : Fin (n+2))
    (i : Fin (n+1)) (v : Fin n → M) :
    pairSlice (normalAt e f r) r i v=(operatorNormalPart e).comp (pairSlice f r i v) := by
  ext a b
  simp only [pairSlice_apply,ContinuousLinearMap.comp_apply,normalAt_insert]
  congr 1

end BoundedHochschild
end
end OAI
