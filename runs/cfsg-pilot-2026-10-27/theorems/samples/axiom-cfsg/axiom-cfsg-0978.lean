public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley

open CFSG.LieType.AlgebraicGroups

section Datum

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_tauF (f : ℕ) (hf : 1 ≤ f) :
    ∃ S : MulAut (adjointGroup TwistTag.E6.tag L), ∀ g : adjointGroup TwistTag.E6.tag L,
      (S g : ModGL TwistTag.E6.tag L) =
        frobTwistGL TwistTag.E6.tag L ℓ f (diagramMap TwistTag.E6 L) g := by
  obtain ⟨S, hS⟩ := ((exceptional_Lang_root_coordinate_surjectivity ℓ L).2.1 TwistTag.E6 f hf 1).1
  refine ⟨S, fun g => ?_⟩
  have h := hS g
  rw [zpow_one] at h
  exact h

end Datum
end CFSG.RankThree.PartOne.KD4L
end
