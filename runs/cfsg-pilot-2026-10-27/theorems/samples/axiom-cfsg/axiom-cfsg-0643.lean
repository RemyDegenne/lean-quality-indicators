public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA.I113

variable {Q : Type} [Group Q] [Finite Q]

section Cases

variable {B M : Subgroup Q} {c : Q}

theorem good_caseI (S : QSetting B M c) (hH3 : Nat.card (t113H B M) ≤ 3) :
    ∃ y w : Q, GoodData B M (t113B0 B M) (ehat c y w) ⊥ M ∧
      t113B0 B M ⊔ ehat c y w ⊔ ⊥ ≤ Subgroup.centralizer (M : Set Q) := by
  have Tr := S.tri
  obtain ⟨y, hy, ho, hnc⟩ := exists_noncentral S.hSyl
  obtain ⟨w, hw, hw3, hwy, hwn⟩ := exists_w S.hSyl hy ho
  have hspec := Triple3.ehat_spec Tr hy ho hnc hw hw3 hwy hwn
  refine ⟨y, w, Triple3.goodData_of_ehat Tr hy ho hnc hw hw3 hwy hwn inf_le_left le_rfl
    (fun b hb => (Tr.B0_mem_A hb).1) (fun z hz e he => (Tr.B0_comm_K hz e (hspec.1 he)).symm) ?_, ?_⟩
  · rw [Tr.card_B]
    calc 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) ≤ 3 * 3 * Nat.card (t113B0 B M) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hH3)
      _ = 9 * Nat.card (t113B0 B M) := by norm_num
  · refine sup_le (sup_le (B0_le_centralizer Tr) fun e he => ?_) bot_le
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hspec.2.2.2 e he l hl).symm

end Cases
end CFSG.LocalAnalysis.GLTheoremA.I1132
end
