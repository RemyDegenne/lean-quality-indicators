public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley

open CFSG.LieType.AlgebraicGroups

section Datum

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

omit [IsAlgClosed L] in
theorem frobTwist_simpleRootSL2 (f : ℕ) (j : Fin TwistTag.E6.tag.rank) (A : SL2 L) :
    frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
        (simpleRootSL2 TwistTag.E6.tag L j A) =
      simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) A) := by
  have h : (frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)).comp
      (simpleRootSL2 TwistTag.E6.tag L j) =
      (simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)).comp
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f)) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
            (simpleRootSL2 TwistTag.E6.tag L j (uSL c)) =
          simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
            (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) (uSL c))
        rw [simpleRootSL2_uSL, map_uSL, simpleRootSL2_uSL]
        exact twistHom_xUnit TwistTag.E6 L (iterateFrobenius L ℓ f) j c
      · change frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L)
            (simpleRootSL2 TwistTag.E6.tag L j (vSL c)) =
          simpleRootSL2 TwistTag.E6.tag L (TwistTag.E6.perm j)
            (Matrix.SpecialLinearGroup.map (iterateFrobenius L ℓ f) (vSL c))
        rw [simpleRootSL2_vSL, map_vSL, simpleRootSL2_vSL]
        exact twistHom_yUnit TwistTag.E6 L (iterateFrobenius L ℓ f) j c
  exact DFunLike.congr_fun h A

end Datum
end CFSG.RankThree.PartOne.KD4L
end
