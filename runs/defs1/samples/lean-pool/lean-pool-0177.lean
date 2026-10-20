@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core.LogReduction

/-- The reduced mantissa m = q * 2^(-k). -/
def reduceMantissa (q : ℚ) : ℚ :=
  if q ≤ 0 then 1  -- Default for non-positive inputs
  else
    let k := reductionExponent q
    q * (2 : ℚ) ^ (-k)

end LeanCert.Core.LogReduction
end
end
end
end
