@[expose] public section

namespace Submonoid

/-- The saturation of a submonoid `s` is the intersection of all saturated submonoids that contain
`s`.

If `M` is a commutative monoid, then this is `{x : M | ∃ y : M, x * y ∈ s}`. -/
@[to_additive
/-- The saturation of an additive submonoid `s` is the intersection of all saturated submonoids
that contain `s`.

If `M` is a commutative additive monoid, then this is `{x : M | ∃ y : M, x + y ∈ s}`. -/]
def saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmonoid M :=
  sInf {t | s ≤ t.toSubmonoid}

end Submonoid
end
