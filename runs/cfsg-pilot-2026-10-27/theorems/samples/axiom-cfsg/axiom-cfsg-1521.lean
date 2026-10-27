public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem genericKill_of_su3_block_odd (hMin : MinIndexU33) [Fact p.Prime] [CharP K p] (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2) {P : Type} [Group P] (α : MulAut P)
    (θ : ↥(StatedSU 3 (p ^ f) K) →* P) (hθ : Function.Injective θ) (hfix : ∀ g, α (θ g) = θ g) :
    GenericKill P α := by
  by_cases hq : 5 ≤ p ^ f
  · exact genericKill_of_su3_block hf hK hp2 hq α θ hθ hfix
  · have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have h2 : 2 ≤ p ^ f := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) p)
    have hq3 : p ^ f = 3 := by omega
    exact genericKill_of_su3_block_of_bad hK hp2 α θ hθ hfix
      (not_kindFactor_statedProj_three_three hMin hK hq3)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
end
