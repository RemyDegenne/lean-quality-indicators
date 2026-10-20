public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace HomologicalComplex

universe uI vI uC vC uD vD uι

variable {I : Type uI} [Category.{vI} I]

variable {C : Type uC} [Category.{vC} C] [Preadditive C]

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

variable [HasColimitsOfShape I C] [HasColimitsOfShape I D]

variable {ι : Type uι} {c : ComplexShape ι}

variable (G : C ⥤ D) [G.Additive]

section HomologyColimit

universe uT vT uA vA uκ

variable {T : Type uT} [Category.{vT} T]

variable {A : Type uA} [Category.{vA} A] [Abelian A]

variable {κ : Type uκ} {shape : ComplexShape κ}

variable [HasColimitsOfShape T A]

@[reassoc]
theorem ofFunctorColimitι_comp_ofFunctorColimIso_hom
    (D : T ⥤ HomologicalComplex A shape) (t : T) :
    ofFunctorColimitι D t ≫ (ofFunctorColimIso D).hom = colimit.ι D t := by
  ext n
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (D ⋙ eval A shape n))
    (isColimitOfPreserves (eval A shape n) (colimit.isColimit D)) t

end HomologyColimit
end HomologicalComplex
end
end
