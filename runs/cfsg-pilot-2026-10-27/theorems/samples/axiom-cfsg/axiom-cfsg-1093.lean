public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

open CFSG.SeitzReduction.LinearPilot (linearSwapDiag linearSwapDiag_apply
  ker_linearSwapDiag_le_center)

open CFSG.Quasithin (perfectCore)

open scoped commutatorElement

section Pair

variable {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem exists_card_subfield_of_sq [Finite K] [CharP K 2] (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ f)
    (k : Subfield K) (hk : Nat.card k ^ 2 = Nat.card K) :
    ∃ f' : ℕ, 2 * f' = f ∧ 1 ≤ f' ∧ Nat.card k = 2 ^ f' ∧
      (Nat.card (StatedSp n k)).factorization 2 = f' * n ^ 2 := by
  have : CharP k 2 := (k.subtype).charP k.subtype_injective 2
  obtain ⟨f', hf', hkc⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have h2 : 2 ^ (f' * 2) = 2 ^ f := by rw [pow_mul, ← hkc, hk, hK]
  have h3 : f' * 2 = f := Nat.pow_right_injective le_rfl h2
  exact ⟨f', by omega, hf', hkc, factorization_card_statedSp hn hkc hf'⟩

end Pair
end CFSG.SeitzReduction.SymplecticPilot
end
