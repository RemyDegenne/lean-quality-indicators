@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace CostructuredArrow

variable {T T' T'' : D} {Y Y' Y'' : C} {S S' : C ⥤ D}

/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[implicit_reducible, simps! left]
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
    (w : S.map g ≫ f'.hom = f.hom := by cat_disch) : f ⟶ f' where
  left := g
  right := 𝟙 f.right

end CostructuredArrow
end CategoryTheory
end
