set_option warningAsError true

@[expose] public section

namespace Bass

universe u v

variable {R : Type u} [Ring R]

/-- A ring is unit-regular when every element has an inner inverse which is a
unit; see Weibel, *The K-book*, Exercise I.1.13(a). -/
def IsUnitRegular (R : Type u) [Ring R] : Prop :=
  ∀ a : R, ∃ x : Rˣ, a = a * (x : R) * a

end Bass
end
