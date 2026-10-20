@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {T : Type u₁} [Category.{v₁} T]

variable {D : Type u₂} [Category.{v₂} D]

namespace CostructuredArrow

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- There is a canonical equivalence between the costructured arrow category with codomain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`. -/
@[simps]
def ofCommaFstEquivalence (c : C) :
    CostructuredArrow (Comma.fst F G) c ≌ Comma (Over.forget c ⋙ F) G where
  functor := ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst
end CostructuredArrow
end CategoryTheory
end
