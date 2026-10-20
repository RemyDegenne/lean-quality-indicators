@[expose] public section

universe u₁ u₂ w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

section

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)]

/-- We say `G` acts naturally on the fibers of `F` if for every `f : X ⟶ Y`, the `G`-actions
on `F.obj X` and `F.obj Y` are compatible with `F.map f`. -/
class IsNaturalSMul : Prop where
  naturality (g : G) {X Y : C} (f : X ⟶ Y) (x : F.obj X) : F.map f (g • x) = g • F.map f x

end
end PreGaloisCategory
end CategoryTheory
end
