public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma tateOpcyclesIsoNegOne_naturality {M N : Rep R G} (f : M ⟶ N) :
    HomologicalComplex.opcyclesMap (tateComplex.map f) (-1) ≫
        (tateOpcyclesIsoNegOne N).hom =
      (tateOpcyclesIsoNegOne M).hom ≫ (Rep.coinvariantsFunctor R G).map f := by
  apply (cancel_epi ((tateComplex M).pOpcycles (-1))).1
  rw [← Category.assoc, HomologicalComplex.p_opcyclesMap]
  rw [pOpcycles_tateOpcyclesIsoNegOne_hom_assoc]
  rw [Category.assoc, pOpcycles_tateOpcyclesIsoNegOne_hom]
  change ((groupHomology.chainsMap (.id G) f).f 0 ≫
      (groupHomology.chainsIso₀ N).hom) ≫ (groupHomology.shortComplexH0 N).g = _
  rw [groupHomology.chainsMap_f_0_comp_chainsIso₀]
  change ((groupHomology.chainsIso₀ M).hom ≫
      (forget₂ (Rep R G) (ModuleCat R)).map f) ≫
      (Rep.coinvariantsMk R G).app N =
    ((groupHomology.chainsIso₀ M).hom ≫ (Rep.coinvariantsMk R G).app M) ≫
      (Rep.coinvariantsFunctor R G).map f
  simpa only [Category.assoc] using congrArg
    (fun k ↦ (groupHomology.chainsIso₀ M).hom ≫ k)
    ((Rep.coinvariantsMk R G).naturality f)

end FiniteGroupTateCohomology
end
