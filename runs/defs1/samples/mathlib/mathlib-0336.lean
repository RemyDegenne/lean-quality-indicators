@[expose] public section

open CategoryTheory Limits

universe w v u

variable {R : Type u} [CommRing R]

namespace CommAlgCat

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

attribute [instance] commRing algebra

/-- Build an `AlgEquiv` from an isomorphism in the category `CommAlgCat R`. -/
@[simps]
def algEquivOfIso (i : A ≅ B) : A ≃ₐ[R] B where
  __ := i.hom.hom
  toFun := i.hom
  invFun := i.inv
  left_inv x := by simp
  right_inv x := by simp

end CommAlgCat
end
