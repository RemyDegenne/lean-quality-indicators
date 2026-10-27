set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {R : Type u} [Ring R]

variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The canonical coefficient lift of an ambient matrix congruent to the
identity modulo `I`. -/
def liftCongruenceEntry (I : TwoSidedIdeal R)
    (u : congruenceSubgroup (n := n) I) (i j : n) :
    Unitization ℤ I :=
  Unitization.mk
    ((1 : Matrix n n ℤ) i j,
      ⟨(u.1 : Matrix n n R) i j - (1 : Matrix n n R) i j,
        congruenceSubgroup_entry_sub_mem I u i j⟩)

end Matrix.GeneralLinearGroup
end
