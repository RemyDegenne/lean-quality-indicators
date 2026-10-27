public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

open CFSG.Assembly.LowTwoRank

open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus projImage)

namespace Step1911EndProof

open Matrix

section KStar

variable {G : Type} [Group G] {L K : Subgroup G}

theorem mem_theta_of_phiL_eq_one [Finite G] (hLK : L ≤ K) {l : L} (hl : phiL hLK l = 1) :
    l ∈ aschbacherSolvableCore 3 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have h2 : IsPGroup 2 (phiL hLK).ker := by
    intro x
    have hx := (phiL_eq_one_iff hLK x).mp (MonoidHom.mem_ker.mp x.2)
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hle : (phiL hLK).ker ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, h2⟩
  exact hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num) (hle hl)

end KStar
end Step1911EndProof
end CFSG.RankThree.PartTwo.Sec19
end
