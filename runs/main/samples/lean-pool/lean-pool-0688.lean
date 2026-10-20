@[expose] public section

namespace NRR

variable {p : Nat}

namespace FoxNeuwirth

noncomputable section

theorem signedIncidence_ne_zero_iff
    (a b : BarredPermutation p) :
    signedIncidence a b ≠ 0 ↔ a.IsFacet b := by
  by_cases h : a.IsFacet b
  · simp [signedIncidence, h]
  · simp [signedIncidence, h]

end
end FoxNeuwirth
end NRR
end
