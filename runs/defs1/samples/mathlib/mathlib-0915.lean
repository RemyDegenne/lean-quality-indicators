@[expose] public section

open CategoryTheory

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where
  obj X := ↧(Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

end CommGrpCat
end
