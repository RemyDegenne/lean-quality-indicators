public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Inner

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.ProperTwoGeneratedCore.CosetNormalizer

open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame

open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model

open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.RootCenter CFSG.SolvableHall

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Hull

variable {K : Type} [Field K] [Finite K] [CharP K 2] {J : HermitianForm 3 K}

theorem odd_torus_order {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) := by
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right 3 (2 ^ f + 1)
  have hpos : 0 < Nat.gcd 3 (2 ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hdiv : (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) = m :=
    Nat.div_eq_of_eq_mul_left hpos (hm.trans (mul_comm _ _))
  rw [hdiv]
  rw [hm] at hodd
  exact (Nat.odd_mul.mp hodd).2

end Hull
end CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Inner
end
