@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

section Finite

variable [Finite ι] [∀ i, (val i).RankOne]
  (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

include hindep

/-- Quotient by the joint residue kernel identifies with the full residue product. -/
noncomputable def quotientIntersectionResidueProductEquiv :
    intersectionSubring val ⧸ RingHom.ker (intersectionResidueProduct val) ≃+*
      (∀ i, IsLocalRing.ResidueField (val i).valuationSubring) :=
  RingHom.quotientKerEquivOfSurjective (intersectionResidueProduct_surjective val hindep)

end Finite
end Valuation
end
