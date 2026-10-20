set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

@[simp]
theorem liftCongruenceEntry_fst (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) (i j : n) :
    (liftCongruenceEntry I u i j).fst =
      (1 : Matrix n n ℤ) i j := rfl

end Matrix.GeneralLinearGroup
end
