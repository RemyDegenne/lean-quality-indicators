public section

noncomputable section

open CategoryTheory.MonoidalCategory Algebra

open Algebra.GrothendieckAddGroup

namespace CategoryTheory.MonoidalGroupCompletion

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C]

variable [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

variable (F : C ⥤ D) [F.Monoidal]

/-- The skeleton monoid homomorphism, transported to additive notation. -/
def skeletonMap : Additive (Skeleton C) →+ Additive (Skeleton D) :=
  (Skeleton.monoidHom F).toAdditive

end CategoryTheory.MonoidalGroupCompletion
end
end
