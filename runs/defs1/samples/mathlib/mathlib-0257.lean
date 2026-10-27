@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]

variable {A' : Type u₂} [Category.{max v₁ u₁} A']

variable {B : Type u₃} [Category.{v₃} B]

variable (J : GrothendieckTopology C)

variable {U : C} (R : Presieve U)

variable (P : Cᵒᵖ ⥤ A) (P' : Cᵒᵖ ⥤ A')

section

variable [HasProducts.{max u₁ v₁} A]

variable [HasProducts.{max u₁ v₁} A']

variable [HasPullbacks C]

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₀*` there."]
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

end
end Presheaf
end CategoryTheory
end
end
