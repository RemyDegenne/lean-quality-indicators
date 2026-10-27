public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace HJRes2

theorem isTripleCover_yb_of_isTripleCover {Y B YB Yd : Subgroup G} {b d : G} (hbB : b ∈ B)
    (hb3 : b ^ 3 = 1) (hCB : Subgroup.centralizer (B : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G))
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (htype : Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5)))
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) (hYBYd : YB ≤ Yd)
    (hbYd : b ∈ Subgroup.normalizer (Yd : Set G))
    (hA6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6))) :
    Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∧
      ∀ y ∈ Yd, b * y * b⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Yd := by
  have h3YB : 3 ∣ Nat.card YB := by
    rcases htype with hA6' | hA5
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6'))
    · exact three_dvd_card_of_ydType148 (d := d) (Or.inl hA5)
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hbH : ∀ y ∈ YB, b * y = y * b := by
    intro y hy
    have hyB : y ∈ Subgroup.centralizer (B : Set G) := (hYBC hy).2
    exact Subgroup.mem_centralizer_iff.mp hyB b hbB
  have hbc := forall_mem_theta_of_isTripleCover hb3 hbYd
    (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd) hA6 hYBYd
    (isPerfect_of_mem_thetaComponentsIn hYB) h3YB hbH
  obtain ⟨η⟩ := HJRes148.nonempty_theta_quot_equiv_of_mem_sectionCentralizer hb3 hCB hYB h3YB hYd
    hYBYd hbYd hbc
  refine ⟨?_, hbc⟩
  rcases htype with hA6' | ⟨⟨φ⟩⟩
  · exact hA6'
  · exfalso
    have h1 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 1080 := by
      obtain ⟨hc, ⟨e⟩⟩ := hA6
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)), Nat.card_congr e.toEquiv, hc,
        KFacts.KS14.card_alternatingGroup_six]
    have h2 : Nat.card (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) = 60 := by
      rw [← Nat.card_congr η.toEquiv, Nat.card_congr φ.toEquiv]
      exact KFacts.KS14.card_alternatingGroup_five_seven_ten.1
    omega

end HJRes2
end CFSG.RankThree.PartTwo.Sec14
end
