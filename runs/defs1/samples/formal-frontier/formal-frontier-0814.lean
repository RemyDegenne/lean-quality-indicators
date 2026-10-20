set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- Inclusion of a two-sided ideal as a nonunital algebra map over `ℤ`. -/
def idealInclusion (I : TwoSidedIdeal R) : I →ₙₐ[ℤ] R where
  toFun x := x.1
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl

end Matrix.GeneralLinearGroup
end
