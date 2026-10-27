public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow OuterRow WeaklyClosed)

open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof (Exp3 tup wordExp gA gB d4S0 d4S0_mem d4T0
  d4T0_mem rootDiagUnit_tup_eq_conj exists_conj_d4S0 exists_conj_d4T0 isPointIrreducible_gA
  isPointIrreducible_gB)

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
  (tw_mem_fixedCharTuples_of_vec tw_rootDiagUnit_mem_torus)

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
  (exists_conj_eq_d4S0_or_d4T0)

open scoped Matrix

section OuterRowProof

theorem outerRow_trialityD4 :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
      p ≠ 2 → p ≠ 3 → OuterRow S := by
  intro S _ _ p f h hp2 hp3
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · subst h'
      exact absurd hp (by norm_num)
    · exact h'
  have hm := h.chevalleyExceptionalModel (by decide)
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (p ^ f) := hm.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (hx y)
    rw [hZC, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact e.injective (hex.trans (map_one e).symm)
  have hcard : Nat.card S = CFSG.Open.ordTrialityD4 (p ^ f) :=
    CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 hm
  refine CFSG.RankThree.PartTwo.Sec4.RonanK432.outerRow_of_fixed_card_dvd hZ
    fun α hα3 hout => ?_
  have hdvd := CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrder_trialityD4_three_odd_aux
    (CFSG.HardMathSupport.Lang.E6Descent.ellQ1Bound_of_rotLang
      CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds)
    CFSG.HardMathSupport.Lang.E6Descent.minusToralBound
    (CFSG.HardMathSupport.Lang.E6Descent.minusEllBound_of_rotLang
      CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds)
    hp hp5 hf S htw α hα3 hout
  refine ⟨CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α,
    CFSG.Open.ordG2 (p ^ f), fun x => Iff.rfl, hdvd, ?_⟩
  rw [hcard]
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.three_mul_ordG2_dvd_ordTrialityD4 (p ^ f)

end OuterRowProof
end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
end
