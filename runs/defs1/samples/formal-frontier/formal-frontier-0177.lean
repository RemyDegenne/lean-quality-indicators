public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology

universe uR uH uM

variable {R : Type uR} [CommRing R]

variable {H : Type uH} [Group H] [Fintype H]

variable {M : Type uM} [AddCommGroup M] [Module R M]

section Topology

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M]
  [T2Space M]

/-- Algebraic coinvariants equipped with their compact Hausdorff quotient
topology. -/
abbrev finiteCoinvariants (ρ : Representation R H M)
    (hρ : ∀ g : H, Continuous (ρ g)) : CompHausAddCommGrp :=
  CompHausAddCommGrp.quotient (CompHausAddCommGrp.of M)
    (coinvariantsClosedAddSubgroup ρ hρ)

end Topology
end ContinuousGroupCohomology
end
end
