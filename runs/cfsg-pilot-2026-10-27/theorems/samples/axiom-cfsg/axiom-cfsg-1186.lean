public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n

open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}

include H

section Certified

theorem Tg_inf_W (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) :
    conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B := by
  refine le_antisymm (fun x hx => ?_) (le_inf (Subgroup.map_mono H.B_le_T) le_sup_right)
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (le_normalizer_of_comm fun x hx y hy => H.commute_of_conj_le_M h48.leM y hy x hx |>.symm) hx.2
  have haT : a ∈ conjSubgroup g T := by
    have := (conjSubgroup g T).mul_mem hx.1 ((conjSubgroup g T).inv_mem
      (Subgroup.map_mono H.B_le_T hb))
    rwa [mul_inv_cancel_right] at this
  have : a ∈ B ⊓ conjSubgroup g T := ⟨ha, haT⟩
  rw [H.B_inf_Tg hCen hU hP, Subgroup.mem_bot] at this
  rw [this, one_mul]
  exact hb

end Certified
end Hyp4
end CFSG.RankThree.GF2n.Tim78
end
