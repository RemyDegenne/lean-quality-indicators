public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec4

variable {Γ : Type} [Group Γ] [Finite Γ]

section PCoreCenter

theorem exists_pCore_center_eq_zpowers {K : Subgroup Γ} (hKq : IsQuasisimple ↥K)
    (hZK : Nat.card (Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K)) = 3) :
    ∃ z : Γ, z ∈ K ∧ K ≤ Subgroup.centralizer {z} ∧ orderOf z = 3 ∧
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hKq
    (aschbacherSolvableCore 3 ↥K) (Sec4.aschbacherSolvableCore_le_center hKq)
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥K) := by
    have hdvd := Subgroup.card_map_dvd (Subgroup.center ↥K)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))
    rw [← hcen, hZK] at hdvd
    exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 3 h3
  refine ⟨((x : ↥K) : Γ), (x : ↥K).2, ?_, ?_, ?_⟩
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have hKz : K ≤ Subgroup.centralizer {((x : ↥K) : Γ)} := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩)
    have hzo : orderOf ((x : ↥K) : Γ) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    exact Sec10.Step1012ClaimKProof.pCore_center_eq_zpowers hKz (x : ↥K).2 hzo hZK

end PCoreCenter
end CFSG.RankThree.PartTwo.Sec14.Ronan148S
end
