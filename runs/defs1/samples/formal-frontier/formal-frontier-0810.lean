set_option warningAsError true

@[expose] public section

namespace Matrix

open scoped BigOperators

universe uR uM uN

variable {R : Type uR} [Ring R]

variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

variable [DecidableEq n]

/-- The additive corner map on native additive-group quotients. -/
def cornerOnCommutatorQuotient (p : n) :
    (R ⧸ Ring.additiveCommutators R) →+
      (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) :=
  QuotientAddGroup.map _ _ (singleAddMonoidHom p p)
    (additiveCommutators_le_corner_comap p)

end Matrix
end
