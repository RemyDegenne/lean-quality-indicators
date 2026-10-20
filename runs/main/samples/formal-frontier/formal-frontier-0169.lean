public section

set_option warningAsError true

set_option linter.style.haveILetI false

set_option backward.defeqAttrib.useBackward true

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)

theorem isIso_nativeGlobalSectionsComparison
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)) :
    IsIso (nativeGlobalSectionsComparison N c hc) := by
  letI : HasColimitsOfShape J (c.pt.Sheaf (Type v)) :=
    CategoryTheory.Sheaf.instHasColimitsOfShape
  letI : CompactSpace c.pt := compactSpace_conePoint N c hc hstage htransition
  letI : PrespectralSpace c.pt := prespectralSpace_conePoint N c hc hstage htransition
  letI : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_conePoint N c hc hstage htransition
  rw [nativeGlobalSectionsComparison_eq_colimMap_post]
  exact IsIso.comp_isIso' (isIso_colimMap_coneSections N c hc hstage htransition)
    (SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso
      (conePullback (Type v) N c) (⊤ : Opens c.pt)
      (by simpa only [Opens.coe_top] using (isCompact_univ : IsCompact (Set.univ : Set c.pt))))

end AlgebraicGeometry.SheafedSpace
end
end
