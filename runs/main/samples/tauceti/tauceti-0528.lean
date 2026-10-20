public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y : TopCat.{w}}

variable (X : ℤ → Set Y)

@[reassoc (attr := simp)]
lemma singularChainFiltrationIso_hom_comp_singularChainFiltrationι (q : ℤ) :
    (singularChainFiltrationIso R X q).hom ≫ singularChainFiltrationι R X q =
      (singularChainFiltration R X q).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

end TauCeti
end
end
