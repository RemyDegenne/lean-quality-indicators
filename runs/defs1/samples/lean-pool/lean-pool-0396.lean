@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core

namespace IntervalDyadic

/-- Multiply with mantissa normalization (prevents bit explosion) -/
def mulNormalized (I J : IntervalDyadic) (maxBits : Nat := 256) : IntervalDyadic :=
  let result := mul I J
  ⟨result.lo.normalizeDown maxBits, result.hi.normalizeUp maxBits, by
    -- Normalization preserves ordering: lo.normalizeDown ≤ lo ≤ hi ≤ hi.normalizeUp
    calc (result.lo.normalizeDown maxBits).toRat
        ≤ result.lo.toRat := Dyadic.toRat_normalizeDown_le _ _
      _ ≤ result.hi.toRat := result.le
      _ ≤ (result.hi.normalizeUp maxBits).toRat := Dyadic.toRat_normalizeUp_ge _ _⟩

end IntervalDyadic
end LeanCert.Core
end
end
end
end
