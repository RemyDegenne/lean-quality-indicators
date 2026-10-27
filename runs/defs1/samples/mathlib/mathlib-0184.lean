@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable [HasShift C ℤ]

variable (X : C)

section

/-- Given a triangle of the form:
```
      f       g       h
  X  ───> Y  ───> Z  ───> X⟦1⟧
```
applying `invRotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧'     f       g
  Z⟦-1⟧  ───>  X  ───> Y  ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shiftEquiv C 1`)
-/
@[simps!]
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : ℤ)).counitIso.inv.app _)

end
end CategoryTheory.Pretriangulated
end
end
