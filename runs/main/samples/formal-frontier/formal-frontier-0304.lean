@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type w}

theorem productIso_assoc (D : Subfunctor F) (E : Subfunctor G)
    (T : Subfunctor H) :
    (productAssoc D E T).hom ≫ (productIso D (E.product T)).hom ≫
      prod.map (𝟙 D.toFunctor) (productIso E T).hom =
    (productIso (D.product E) T).hom ≫
      prod.map (productIso D E).hom (𝟙 T.toFunctor) ≫
        (prod.associator D.toFunctor E.toFunctor T.toFunctor).hom := by
  simp only [productAssoc, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom]
  simp [Category.assoc]

end CategoryTheory.Subfunctor
end
