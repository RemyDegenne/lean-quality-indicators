public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

open Item148Rank

section Field

theorem not_isInnerAut_of_inducesStdKind_field148 {Γ : Type} [Group Γ] [Finite Γ]
    {X : Subgroup Γ} {x : Γ} (hfield : KFacts.InducesStdKind X x .field)
    (hx : x ∈ Subgroup.normalizer (X : Set Γ)) :
    ¬ KFacts.IsInnerAut (X.normalizerMonoidHom ⟨x, hx⟩) := by
  obtain ⟨hx', hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta X hfield (by decide)
  rintro ⟨w, hw⟩
  apply hnot
  refine ⟨((w : X) : ↥X ⧸ aschbacherSolvableCore 3 ↥X), ?_⟩
  have hc : Sec4.compAction X ⟨x, hx'⟩ = MulAut.conj w := hw.symm
  rw [hc]
  ext q
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, MulAut.conj_apply,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]

end Field
end CFSG.RankThree.PartTwo.Sec14
end
