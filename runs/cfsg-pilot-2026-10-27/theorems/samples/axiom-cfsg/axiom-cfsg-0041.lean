public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint

open scoped commutatorElement

namespace Item211Res2Proof

theorem twoLocalSmall_of_center_quotient {X : Type} [Group X] [Group.IsPerfect X]
    (h : TwoLocalSmall (X ⧸ Subgroup.center X)) : TwoLocalSmall X := by
  refine TwoLocalSmallIn.of_injective h (KFacts.centerDescend X) ?_
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h1 := congrArg (fun φ : MulAut (X ⧸ Subgroup.center X) =>
    φ (s : X ⧸ Subgroup.center X)) hσ
  simp only [KFacts.centerDescend_mk, MulAut.one_apply] at h1
  rw [QuotientGroup.eq] at h1
  have := (Subgroup.center X).inv_mem h1
  simpa using this

end Item211Res2Proof
end CFSG.RankThree.PartTwo.Sec21
end
