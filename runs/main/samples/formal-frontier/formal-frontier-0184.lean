@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

@[simp]
theorem mem_zeroAdditiveSubfunctor_iff (A : ((FGAlgCat.{u} K)ᵒᵖ)ᵒᵖ)
    (x : (additiveTestPoints K).obj A) :
    x ∈ (zeroAdditiveSubfunctor K).obj A ↔ x = (0 : (A.unop.unop.obj : Type u)) := Iff.rfl

end General
end AlgebraicGeometry
end
