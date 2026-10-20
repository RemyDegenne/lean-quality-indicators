public section

open CategoryTheory

universe u w

namespace TauCeti

theorem isGorensteinProjective_of_moduleInjective_self
    (k : Type w) [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
    (hr : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ) (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)
    (M : ModuleCat.{u} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] : IsGorensteinProjective Aᵐᵒᵖ M := by
  let : IsNoetherianRing Aᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  let F := forget₂ (FGModuleCat.{u} Aᵐᵒᵖ) (ModuleCat.{u} Aᵐᵒᵖ)
  obtain ⟨S, hS, hproj, he, ⟨eM⟩⟩ :=
    (FGModuleCat.abelian_isFrobenius k hr hl).exists_projective_conflation_sequence
      (FGModuleCat.of Aᵐᵒᵖ M)
  let T (n : ℤ) := (S n).map F
  let e (n : ℤ) := F.mapIso (he n).some
  have hT (n : ℤ) : (T n).ShortExact :=
    ((ExactStructure.abelian_conflation _).mp (hS n)).map_of_exact F
  let P := CochainComplex.splice T e
  have hfinite (n : ℤ) : Module.Finite Aᵐᵒᵖ (P.X n) := (S n).X₂.property
  have hprojective (n : ℤ) : Projective (P.X n) := by
    have : Projective (S n).X₂ := (ExactStructure.abelian_isProjective_iff _).mp (hproj n)
    have : Module.Projective Aᵐᵒᵖ (S n).X₂ := FGModuleCat.moduleProjective_of_projective _
    exact ModuleCat.projective_of_categoryTheory_projective (R := Aᵐᵒᵖ) (P := (S n).X₂.obj)
  refine (isGorensteinProjective_iff M).mpr ⟨P,
    P.isTotallyAcyclic_of_acyclic_of_moduleInjective_self hr hfinite hprojective
      (CochainComplex.acyclic_splice T e hT), ?_⟩
  exact ⟨(CochainComplex.spliceCyclesIso T e hT 0).symm ≪≫ F.mapIso eM⟩

end TauCeti
end
