@[expose] public section

variable {R : Type*}

namespace MulRingNorm

variable [NonAssocRing R]

variable (R)

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

section MulRingNorm_equiv_AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]

/-- An absolute value defines a multiplicative ring norm. -/
@[simps]
def ofAbsoluteValue (v : AbsoluteValue R ℝ) : MulRingNorm R where
  toFun := v.toFun
  map_zero' := (v.eq_zero' 0).mpr rfl
  add_le' := v.add_le'
  neg' := v.map_neg
  map_one' := v.map_one
  map_mul' := v.map_mul'
  eq_zero_of_map_eq_zero' x := (v.eq_zero' x).mp

end MulRingNorm_equiv_AbsoluteValue
end MulRingNorm
end
