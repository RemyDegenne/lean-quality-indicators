public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {n : ℕ} {K : Type} [Field K]

theorem factorization_two_mul_card_mulAut_statedSp_two_le [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) :
    (2 * Nat.card (MulAut (StatedSp n K))).factorization 2 ≤ n ^ 2 + 1 := by
  have : NeZero n := ⟨by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have hA : Nat.card (MulAut (StatedSp n K)) =
      Nat.card (MulAut (StatedProj (StatedSp n K))) :=
    Nat.card_congr (MulAut.congr (F4Pilot.spProjEquiv n K)).toEquiv
  have h2 := E6Pilot.card_mulAut_dvd_card_mul_card_outer (StatedProj (StatedSp n K))
  have h3 := (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.outer_card_dvd Nat.prime_two
    le_rfl hK1 (by omega)).2 hn
  rw [gcd_two_two_pow_sub_one le_rfl, mul_one] at h3
  have hP : Nat.card (StatedProj (StatedSp n K)) = Nat.card (StatedSp n K) :=
    (Nat.card_congr (F4Pilot.spProjEquiv n K).toEquiv).symm
  have h4 : 2 * Nat.card (MulAut (StatedSp n K)) ∣ 2 * Nat.card (StatedSp n K) := by
    rw [hA, ← hP]
    refine Nat.mul_dvd_mul_left 2 (h2.trans ?_)
    rw [Nat.dvd_one.1 h3, mul_one]
  have hS0 : Nat.card (StatedSp n K) ≠ 0 := Nat.card_pos.ne'
  have hA0 : 2 * Nat.card (MulAut (StatedSp n K)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    rw [hA]
    have : Finite (StatedProj (StatedSp n K)) :=
      Finite.of_equiv _ (F4Pilot.spProjEquiv n K).toEquiv
    exact Nat.card_pos.ne'
  have h5 := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero two_ne_zero hS0)).2 h4 2
  rw [Nat.factorization_mul two_ne_zero hS0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    factorization_card_statedSp (by omega) hK1 le_rfl, one_mul] at h5
  omega

end CFSG.SeitzReduction.SymplecticPilot
end
