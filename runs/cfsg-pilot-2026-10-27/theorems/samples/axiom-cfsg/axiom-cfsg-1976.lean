public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

section Solv

theorem isSolvable_quaternion_two : Group.IsSolvable (QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (QuaternionGroup 2) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have := hp.isNilpotent
  infer_instance

end Solv
end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
end
