public noncomputable section

open Cardinal

open HahnSeries.CardSuppLTTruncationIntegerPart

namespace ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement

universe u v

variable {G : Type u} {R : Type v}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

variable [Module ℚ G] [IsOrderedModule ℚ G]

variable [Field R]

local instance : PosSMulStrictMono ℚ G := PosSMulMono.toPosSMulStrictMono

theorem assumptionA3_iff {Z : Subring R} :
    AssumptionA3 Z ↔
      ∀ z a b : Z, z ∣ a * b →
        ∃ z₁ z₂ : Z, z₁ ∣ a ∧ z₂ ∣ b ∧ z = z₁ * z₂ :=
  Iff.rfl

end ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement
end
