@[expose] public section

namespace Submonoid

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
/-- The center of an addition with zero `M` is the set of elements that commute with everything in
`M` -/]
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center
  mul_mem' := Set.mul_mem_center

end MulOneClass
end Submonoid
end
