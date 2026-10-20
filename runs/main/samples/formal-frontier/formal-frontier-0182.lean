@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G H : Cᵒᵖ ⥤ Type w}

@[reassoc (attr := simp)]
theorem productIso_hom_comp_map_ι (D : Subfunctor F) (E : Subfunctor G) :
    (productIso D E).hom ≫ prod.map D.ι E.ι = (D.product E).ι := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc,
      productIso_hom_fst, productFst_comp_ι]
  · rw [Category.assoc, prod.map_snd, ← Category.assoc,
      productIso_hom_snd, productSnd_comp_ι]

end CategoryTheory.Subfunctor
end
