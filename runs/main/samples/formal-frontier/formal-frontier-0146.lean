@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

universe v u w

namespace CategoryTheory.CartesianMonoidalCategory

variable {K : Type u} [Category.{v} K] [CartesianMonoidalCategory K]
  [HasBinaryProducts K]

@[reassoc (attr := simp)]
theorem tensorLeftIsoProd_hom_app_fst (A B : K) :
    (tensorLeftIsoProd A).hom.app B ≫ prod.fst = fst A B :=
  (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) ⟨.left⟩

end CategoryTheory.CartesianMonoidalCategory
end
