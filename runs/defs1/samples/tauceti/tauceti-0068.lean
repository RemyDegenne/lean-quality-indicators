public section

namespace TauCeti.ContCohomology

universe uG uM uM' uN uN' uA uB uC

section DualityMapTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **Tate's duality map in degree `2`**,
`α₂ : H²(G, M) → Hom(H⁰(G, InternalHom G M N), H²(G, N))`: the `(2,0)` cup along the opposite
evaluation pairing, `α₂ b φ = ⟨b, φ⟩`, the class of the cocycle `(g, h) ↦ φ (b (g, h))` for an
invariant `φ`. -/
noncomputable def dualityMap2 : H2 G M →+ H0 G (InternalHom G M N) →+ H2 G N :=
  explicitCup20 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

end DualityMapTwo
end TauCeti.ContCohomology
end
