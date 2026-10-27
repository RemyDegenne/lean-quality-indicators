public section

namespace CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.B.Classical.E6Adjoint

theorem glMatT_genY
    {k : ℕ} (hk : k < 72) : glMatT (genY k) = toMat (nGen k) := by
  have h1 : (1 : C2E6Overlap.K) = ofBits true false := ofBits_true_false.symm
  unfold genY nGen
  split_ifs with h
  · rw [h1]
    exact glMatT_pinnedX_root hk true false
  · rw [map_mul, h1, toMat_mul]
    exact congrArg₂ (· * ·) (glMatT_pinnedX_root hk true false)
      (glMatT_pinnedX_root (rhoIdx_lt hk) true false)

end CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two
end
