@[expose] public section

open CategoryTheory SimplicialObject MonoidalCategory Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y : SSet.{u}}

/-- The type of homotopies between morphisms `X ⟶ Y` of simplicial sets.
The data consists of a morphism `h : X ⊗ Δ[1] ⟶ Y` which induces
both `f` and `g`, see the lemmas `SSet.Homotopy.h₀` and `SSet.Homotopy.h₁`. -/
def Homotopy (f g : X ⟶ Y) : Type u :=
  (RelativeMorphism.botEquiv.symm f).Homotopy (RelativeMorphism.botEquiv.symm g)

end SSet
end
