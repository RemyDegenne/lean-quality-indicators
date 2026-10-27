set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

/-- A two-sided ideal is right quasi-regular if each `x` in it has a
right quasi-inverse `y` in the ideal, so `(1 + x) * (1 + y) = 1`. -/
def IsRightQuasiregular (I : TwoSidedIdeal R) : Prop :=
  ∀ x : R, x ∈ I → ∃ y : R, y ∈ I ∧ x + y + x * y = 0

end TwoSidedIdeal
end
