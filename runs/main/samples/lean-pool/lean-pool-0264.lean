@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Johnson

section

open scoped BigOperators InnerProductSpace Matrix

theorem coordinateSplitEquiv_card {n w : ℕ}
    (x : JohnsonSphere n w) (S : Finset (Fin n)) :
    ((coordinateSplitEquiv x S).1).card +
      ((coordinateSplitEquiv x S).2).card = S.card := by
  change
    (((coordinateSumEquiv x).symm.finsetCongr S).toLeft).card +
      (((coordinateSumEquiv x).symm.finsetCongr S).toRight).card =
        S.card
  rw [Finset.card_toLeft_add_card_toRight]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

end
end Johnson
end MetricCodes
end MetricCodesNoncomputable
end
