public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.GrpObj

open MonoidalCategory CartesianMonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The left-translation isomorphism `(f * ·)` of a group object.
For algebraic groups and rational points, see Milne, *Algebraic Groups* (2017), item 1.8. -/
@[to_additive /-- The left-translation isomorphism `(f + ·)` of an additive group object. -/]
def mulLeft {A : C} [GrpObj A] (f : 𝟙_ C ⟶ A) : A ≅ A :=
  asIso ι[A] ≪≫ mulRight (f ≫ ι[A]) ≪≫ asIso ι[A]

end CategoryTheory.GrpObj
end
end
