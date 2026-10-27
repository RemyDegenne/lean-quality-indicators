namespace P2MW.S_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le

attribute [-instance] instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace OrdCountAsm

noncomputable section

section Galois

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)

variable (V₁ : Submodule k ρbar.V)

def iota (hstab : HStab p ρbar V₁) :
    cocycles₁ (Nrep p ρbar V₁ hstab) →ₗ[k] cocycles₁ (AdL p ρbar) where
  toFun y := ⟨fun g => ((toNilp p ρbar V₁ hstab (y.val g) : nilp V₁) : Module.End k ρbar.V), by
    rw [mem_cocycles₁_iff]
    intro g h
    exact congrArg (fun m => ((toNilp p ρbar V₁ hstab m : nilp V₁) : Module.End k ρbar.V))
      ((mem_cocycles₁_iff y.val).mp y.2 g h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Galois
end
end OrdCountAsm
end P2MW.S_ResidualGaloisRep_finiteDimensional_ordinaryUnitClassesAd_and_finrank_le
