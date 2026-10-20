@[expose] public section

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

theorem shuffleRank_apply_right
    (hp : Nat.Prime p) (a : BarredPermutation p)
    (ha : a.dualDimension = p - 2)
    (s : ShuffleIndex p (facetLeftSize hp a ha))
    (i : Fin p) (hi : ¬ (a.rank i).1 < facetLeftSize hp a ha) :
    shuffleRank hp a ha s i =
      s.1ᶜ.orderEmbOfFin (shuffle_compl_card hp a ha s)
        ⟨(a.rank i).1 - facetLeftSize hp a ha, by
          have _hirank := (a.rank i).2
          have hk := facetLeftSize_lt hp a ha
          omega⟩ := by
  simp [shuffleRank, facetLabelSumEquiv, shuffleMergeEquiv, hi,
    finSumEquivOfFinset_inr]

end FoxNeuwirth
end NRR
end
