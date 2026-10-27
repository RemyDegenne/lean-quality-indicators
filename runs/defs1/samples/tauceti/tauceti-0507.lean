public section

namespace TauCeti.ContCohomology

open TopRep

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous function `f : G × G → ZMod 2`, as the homogeneous `2`-cochain
`(g₀, g₁, g₂) ↦ f (g₀⁻¹ * g₁, g₁⁻¹ * g₂)` of the trivial `𝔽₂` coefficients `trivialF2 G`, lifted
to their carrier. -/
noncomputable def inhomogeneousCochain2 (f : G × G → ZMod 2) (hf : Continuous f) :
    (homogeneousCochains (trivialF2 G)).X 2 :=
  ⟨ContinuousMap.curry <| ContinuousMap.curry
      ⟨fun q : (G × G) × G ↦ (trivialF2Equiv G).symm (f (q.1.1⁻¹ * q.1.2, q.1.2⁻¹ * q.2)),
        continuous_of_discreteTopology.comp (hf.comp
          ((continuous_fst.comp continuous_fst).inv.mul (continuous_snd.comp continuous_fst)
            |>.prodMk ((continuous_snd.comp continuous_fst).inv.mul continuous_snd)))⟩,
    fun g ↦ by
      ext h₀ h₁ h₂
      simp only [ContRepresentation.coind₁_apply_apply, trivialF2_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]⟩

end TauCeti.ContCohomology
end
