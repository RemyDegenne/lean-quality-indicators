set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uS

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Semiring

variable [Semiring R]

@[simp]
theorem stabilize_apply_inl_inl (g : GL X R) (i j : X) :
    stabilize (Y := Y) g (Sum.inl i) (Sum.inl j) = g i j := rfl

end Semiring
end Matrix.GeneralLinearGroup
end
