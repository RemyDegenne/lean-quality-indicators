@[expose] public section

universe v₁ v₂ u₁ u₂

open Opposite

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.Functor

variable [Category.{v₁} C]

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

variable (C D)

variable {C D}

section

variable (C)

/-- `Functor.leftOp` sends identity functors to the canonical isomorphism `unopUnop`. -/
@[simps!]
def leftOpId : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C := Iso.refl _

end
end
end Functor
end CategoryTheory
end
