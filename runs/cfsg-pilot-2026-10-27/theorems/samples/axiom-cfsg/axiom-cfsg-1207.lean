public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.AGLEmbeddingD2.SquareSpinMinus
  CFSG.ClassicalInvolution.Q3.Q3TW CFSG.LieType.CurtisTits
  CFSG.Timmesfeld.ClassicalOrders CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

variable {F : Type} [Field F] {b c : F}

theorem deletionIsometry_apply_inr_inl_succ (r : ℕ) (b c : F) (v : Vm (r + 1) F)
    (j : Fin r) :
    deletionIsometry r b c v (Sum.inr (Sum.inl (Fin.succ j))) = v (Sum.inr (Sum.inl j)) := by
  change (minusSplit F r).symm ((0, 0), v) (Sum.inr (Sum.inl (Fin.succ j))) =
    v (Sum.inr (Sum.inl j))
  rfl

end CFSG.RankThree.PartOne.KCOrthogonal
end
