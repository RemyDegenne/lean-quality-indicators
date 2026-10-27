namespace P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ProperCurveExtension

variable {K : Type u} [Field K]

section Totalise

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
  [IsIntegral X] [IsProper sY] (hval : ∀ x : X, ValuationRing (X.presheaf.stalk x))
  (f : X.PartialMap Y) (hf : f.hom ≫ sY = f.domain.ι ≫ sX)

def extend : X ⟶ Y :=
  haveI : Y.IsSeparated := isSeparated_of_isSeparated_over sY
  X.topIso.inv ≫ X.homOfLE (domain_eq_top sX sY hval f hf).ge ≫ f.toRationalMap.toPartialMap.hom

end Totalise
end ProperCurveExtension
end
end P2MW.S_AlgebraicGeometry_Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper
