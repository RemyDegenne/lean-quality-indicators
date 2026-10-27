public section

namespace TauCeti.ContCohomology

open TopRep

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous function `f : G → ZMod 2`, as the homogeneous `1`-cochain
`(g₀, g₁) ↦ f (g₀⁻¹ * g₁)` of the trivial `𝔽₂` coefficients `trivialF2 G`, lifted to their
carrier.

Source: this constructor is close to the degree-`1` constructor of Tau Ceti PR
[#11157](https://github.com/TauCetiProject/TauCeti/pull/11157); here it is stated on
`homogeneousCochains (trivialF2 G)` directly, without local compactness, with
`inhomogeneousCochain2` as its degree-`2` counterpart. -/
noncomputable def inhomogeneousCochain1 (f : G → ZMod 2) (hf : Continuous f) :
    (homogeneousCochains (trivialF2 G)).X 1 :=
  ⟨ContinuousMap.curry ⟨fun q : G × G ↦ (trivialF2Equiv G).symm (f (q.1⁻¹ * q.2)),
      continuous_of_discreteTopology.comp (hf.comp (continuous_fst.inv.mul continuous_snd))⟩,
    fun g ↦ by
      ext h₀ h₁
      simp only [ContRepresentation.coind₁_apply_apply, trivialF2_ρ_apply_apply,
        ContinuousMap.curry_apply, ContinuousMap.coe_mk, mul_inv_rev, inv_inv, mul_assoc,
        mul_inv_cancel_left]⟩

end TauCeti.ContCohomology
end
