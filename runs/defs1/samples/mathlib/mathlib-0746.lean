@[expose] public section

namespace CategoryTheory

open Category

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

variable {T : Type u₃} [Category.{v₃} T]

variable {A' : Type u₄} [Category.{v₄} A']

variable {B' : Type u₅} [Category.{v₅} B']

variable {T' : Type u₆} [Category.{v₆} T']

variable {L : A ⥤ T} {R : B ⥤ T}

namespace Comma

variable (L) (R)

section Opposite

open Opposite

/-- The canonical functor from `Comma L.op R.op` to `(Comma R L)ᵒᵖ`. -/
@[implicit_reducible, simps]
def unopFunctor : Comma L.op R.op ⥤ (Comma R L)ᵒᵖ where
  obj X := ⟨X.right.unop, X.left.unop, X.hom.unop⟩
  map f := ⟨f.right.unop, f.left.unop, Quiver.Hom.op_inj (by simpa using! f.w.symm)⟩

end Opposite
end Comma
end CategoryTheory
end
