namespace P2MW.S_ModularForm_etaProductEleven_pow_twelve_smul

set_option autoImplicit false

p2m_open

open UpperHalfPlane hiding I

open scoped Real ModularForm MatrixGroups Topology Manifold

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

p2m_reactivate

namespace ModularCurve

theorem etaProductIsCuspForm_of_trivial (h : EtaMultiplierTrivial)
    (hcusp : EtaProductVanishesAtCusps) : EtaProductIsCuspForm := by
  refine ⟨{ toFun := fun τ : ℍ => etaProductEleven (τ : ℂ)
            slash_action_eq' := ?_
            holo' := mdifferentiable_etaProductEleven
            zero_at_cusps' := fun {c} hc => hcusp hc }, fun z => rfl⟩
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
  exact slashInvariant_of_etaMultiplierTrivial h hγ

end ModularCurve
end
end P2MW.S_ModularForm_etaProductEleven_pow_twelve_smul
