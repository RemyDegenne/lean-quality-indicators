public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma tateCyclesIsoZero_naturality {M N : Rep R G} (f : M ⟶ N) :
    HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
        (tateCyclesIsoZero N).hom =
      (tateCyclesIsoZero M).hom ≫ (Rep.invariantsFunctor R G).map f := by
  let _ : Mono (ModuleCat.ofHom N.ρ.invariants.subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  apply (cancel_mono (ModuleCat.ofHom N.ρ.invariants.subtype)).1
  change HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
      ((tateCyclesIsoZero N).hom ≫ (groupCohomology.shortComplexH0 N).f) =
    (tateCyclesIsoZero M).hom ≫
      ((Rep.invariantsFunctor R G).map f ≫ ModuleCat.ofHom N.ρ.invariants.subtype)
  rw [tateCyclesIsoZero_hom_inclusion, invariantsMap_inclusion]
  change (HomologicalComplex.cyclesMap (tateComplex.map f) 0 ≫
        (tateComplex N).iCycles 0) ≫ (groupCohomology.cochainsIso₀ N).hom =
    ((tateCyclesIsoZero M).hom ≫ (groupCohomology.shortComplexH0 M).f) ≫
      f.toModuleCatHom
  rw [tateCyclesIsoZero_hom_inclusion]
  rw [HomologicalComplex.cyclesMap_i]
  change (tateComplex M).iCycles 0 ≫
      ((groupCohomology.cochainsMap (.id G) f).f 0 ≫
        (groupCohomology.cochainsIso₀ N).hom) =
    (tateComplex M).iCycles 0 ≫
      ((groupCohomology.cochainsIso₀ M).hom ≫ f.toModuleCatHom)
  rw [groupCohomology.cochainsMap_f_0_comp_cochainsIso₀]

end FiniteGroupTateCohomology
end
