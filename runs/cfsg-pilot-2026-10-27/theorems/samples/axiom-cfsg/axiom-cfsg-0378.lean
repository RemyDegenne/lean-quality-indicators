public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP.SeitzToral CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel Matrix

namespace GenLocDiagU

variable {K : Type} [Field K]

theorem unitaryFieldData_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    UnitaryFieldData p f K := by
  refine ⟨hp, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h0
  have hf : f = 0 := by omega
  subst hf
  have : Nat.card K = 1 := by simpa using hK
  exact (not_subsingleton K) (Nat.card_eq_one_iff_unique.1 this).1

end GenLocDiagU
end CFSG.GH74.Generic.BProg.B2
end
