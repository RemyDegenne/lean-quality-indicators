@[expose] public section

open OrderDual Opposite Set

universe u

open CategoryTheory

attribute [instance] BoolAlg.str

/-- The powerset functor. `Set` as a contravariant functor. -/
@[simps]
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
  obj X := op ↧(Set X)
  map {X Y} f := Quiver.Hom.op (BoolAlg.ofHom (CompleteLatticeHom.setPreimage f))

end
