@[expose] public section

set_option linter.style.haveILetI false

open scoped Topology

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

noncomputable section

universe u v

namespace ValuationRing

/-- The valuation-integer subring in the completion of the fraction field of a valuation ring. -/
noncomputable def CompletionIntegers
    (V : Type u) (K : Type v) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
    Subring (UniformSpace.Completion K) := by
  letI : Valued K (ValueGroup V K) := Valued.mk' (valuation V K)
  exact Valued.integer (UniformSpace.Completion K)

end ValuationRing
end
end
