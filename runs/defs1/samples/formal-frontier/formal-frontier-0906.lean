@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

section FiniteRankLeOne

variable [Finite ι] [∀ j, (val j).RankLeOne]

variable (i : ι) [(val i).IsNontrivial]

/-- Quotient by the contracted ideal at a nontrivial place gives its full residue field. -/
noncomputable def quotientContractedIdealEquivOfRankLeOne :
    intersectionSubring val ⧸ contractedIdeal val i ≃+*
      IsLocalRing.ResidueField (val i).valuationSubring :=
  RingHom.quotientKerEquivOfSurjective (intersectionResidueMap_surjective_of_rankLeOne val i)

end FiniteRankLeOne
end Valuation
end
