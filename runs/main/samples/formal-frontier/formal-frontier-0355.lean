set_option warningAsError true

@[expose] public section

open Function

open scoped BigOperators

namespace Bass

universe u v

theorem stableRange_eq_quotient
    {R : Type u} [Ring R] (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) {sR sQ : ℕ}
    (hR : IsStableRange R sR)
    (hQ : IsStableRange (R ⧸ I.asIdeal) sQ) : sR = sQ := by
  apply le_antisymm
  · exact hR.2 sQ ((stableRangeCondition_quotient_iff I hI sQ).mpr hQ.1)
  · exact hQ.2 sR ((stableRangeCondition_quotient_iff I hI sR).mp hR.1)

end Bass
end
