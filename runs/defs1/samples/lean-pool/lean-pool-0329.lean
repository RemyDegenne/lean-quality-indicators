@[expose] public section

noncomputable section

open CategoryTheory Finset

open CategoryTheory.Localization.Construction

universe v u v' pu pv u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory.Dilatations

variable {C : Type u} [Category.{v} C]

variable (Z : Center C)

variable {D : Type u} [Category.{v'} D]

variable (F : C ⥤ D)

/-- **Proposition 3.14.** The canonical functor `Φ : C[{dᵢ}_{i∈K}] ⥤ C[{dᵢ}_{i∈I}]`. -/
noncomputable def restrictPhi (Z : Center C) (K : Set Z.I) (hK : K.Nonempty) :
    Dila (Z.restrict K hK) ⥤ Dila Z :=
  DilaLift (Z.restrict K hK) (CatToDila Z)
    (by show (ImageCenterLocalizationFunctor (Z.restrict K hK) (CatToDila Z)).Faithful
        exact CatToDila_isSigmaRegular_restrict Z K hK)
    (CatToDila_restrict_hsieve Z K hK)

end CategoryTheory.Dilatations
end
end
