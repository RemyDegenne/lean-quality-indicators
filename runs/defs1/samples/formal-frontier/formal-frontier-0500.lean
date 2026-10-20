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

/-- The canonical comparison is an isomorphism when the mapped functor
preserves the colimit of every term. -/
@[expose] noncomputable def colimMapIso (K : HomologicalComplex (I ⥤ C) c)
    [∀ n, PreservesColimit (K.X n) G] :
    ((colim (J := I) (C := D)).mapHomologicalComplex c).obj
        (((Functor.whiskeringRight I C D).obj G).mapHomologicalComplex c |>.obj K) ≅
      (G.mapHomologicalComplex c).obj
        (((colim (J := I) (C := C)).mapHomologicalComplex c).obj K) :=
  asIso (colimMapComparison G K)

end HomologicalComplex
end
end
