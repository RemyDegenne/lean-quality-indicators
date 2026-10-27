@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core.IntervalRat

/-- The rational lower bound for twice π used in argument reduction. -/
def twoPiRatLo : ℚ := LeanCert.Core.TrigReduction.twoPiRatLo

end LeanCert.Core.IntervalRat
end
end
end
end
