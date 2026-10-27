public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KLCE

open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.LocalAnalysis.ComponentInitial (sl2_closure_upper_lower)

open CFSG.RankThree.PartOne.TCX

open scoped MatrixGroups

section Root

variable {L : Type} [Field L] [CharP L 2]

theorem triP_conj_rootSL2 {θ : Fin TwistTag.D4.tag.rank → ℤ} (hθ : IsRoot TwistTag.D4.tag θ)
    (hρ : permLattice TwistTag.D4.perm θ = θ) (B : SL(2, L)) :
    triP L * rootSL2 TwistTag.D4.tag L θ B * (triP L)⁻¹ = rootSL2 TwistTag.D4.tag L θ B := by
  have hρ' : permLattice TwistTag.D4.perm (-θ) = -θ := by
    rw [show permLattice TwistTag.D4.perm (-θ) = -permLattice TwistTag.D4.perm θ from by
      funext i
      simp [permLattice], hρ]
  let f : SL(2, L) →* ModGL TwistTag.D4.tag L :=
    (MulAut.conj (triP L)).toMonoidHom.comp (rootSL2 TwistTag.D4.tag L θ)
  have hfg : f = rootSL2 TwistTag.D4.tag L θ := by
    refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := L)) ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change triP L * rootSL2 TwistTag.D4.tag L θ (uSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L θ (uSL c)
      rw [rootSL2_uSL_of_charTwo hθ, triP_conj_pinnedX hθ, hρ]
    · change triP L * rootSL2 TwistTag.D4.tag L θ (vSL c) * (triP L)⁻¹ =
        rootSL2 TwistTag.D4.tag L θ (vSL c)
      rw [rootSL2_vSL_of_charTwo hθ, triP_conj_pinnedX (IsRoot.neg hθ), hρ']
  exact DFunLike.congr_fun hfg B

end Root
end CFSG.RankThree.PartOne.TCX.Tri
end
