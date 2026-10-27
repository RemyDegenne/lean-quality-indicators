public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG

open scoped Matrix

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem mp_class_witness {W w₀ : WeylGroup TwistTag.D4.tag}
    (hw₀ : ∀ x : Fin TwistTag.D4.tag.rank → ℤ, w₀ • x = -x)
    (hW : (∀ x, W • x = d4MatThreeA *ᵥ x) ∨ (∀ x, W • x = d4MatThreeB *ᵥ x)) :
    ∃ u : WeylGroup TwistTag.D4.tag, ∀ x,
      (u * (W⁻¹ * w₀) * (weylTwist TwistTag.D4 u)⁻¹) • x =
        d4T36M (-1) *ᵥ permLattice TwistTag.D4.perm.symm x := by
  obtain ⟨u, hu⟩ := q1_class_witness hW
  refine ⟨u, fun x => ?_⟩
  have h1 : (u * (W⁻¹ * w₀) * (weylTwist TwistTag.D4 u)⁻¹) • x =
      -((u * W⁻¹ * (weylTwist TwistTag.D4 u)⁻¹) • x) := by
    simp only [mul_smul, hw₀, smul_neg]
  rw [h1, hu x]
  have h2 : d4T36M (-1) = -d4T36M 1 := by simp [d4T36M]
  rw [h2, Matrix.neg_mulVec]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
end
