public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.Coordinator

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Frame

theorem setupRigid_E6_two {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) e6PhiTwoWeyl)
    (hK4 : 4 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8) {p : ℕ} (hp2 : p ≠ 2)
    (hpq1 : p ∣ Nat.card K + 1) [IsAlgClosed (AlgebraicClosure K)]
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiTwoWeyl hg0C hg0) :
    SetupRigid S := by
  obtain ⟨D, ρ, frob, E, hp, hq, hqpow, hpq, hfin, hEle, hEexp, hEall⟩ := S
  simp only at hSD
  subst hSD
  obtain ⟨Z, hZΓ, hZp, hZspan, hZord, hrig⟩ := exists_rigid_frame_E6_two hFr hg0C hg0 hK4 hK8
  refine setupRigid_of_frame _ Z (fun i => Pi.single i 1) (fun i => isRoot_single _ i) hZΓ hZp
    (fun i => ?_) (fun i => hZord p hp hp2 hpq1 i) hrig
  have hρ := frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 frob (isRoot_single _ i)
  change Z i ≤ rootSpan Tag.E6 _
    {Pi.single i 1, -Pi.single i 1, ρ (Pi.single i 1), -ρ (Pi.single i 1)}
  rw [hρ]
  exact hZspan i

end Frame
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
