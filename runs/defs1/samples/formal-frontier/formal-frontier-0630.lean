set_option warningAsError true

@[expose] public section

namespace Matrix

open scoped BigOperators

universe uR uM uN

variable {R : Type uR} [Ring R]

variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

variable [DecidableEq n]

/-- The trace homomorphism on additive commutator quotients, including empty indices. -/
def traceOnCommutatorQuotient :
    (Matrix n n R ⧸ Ring.additiveCommutators (Matrix n n R)) →+
      (R ⧸ Ring.additiveCommutators R) :=
  QuotientAddGroup.map _ _ (traceAddMonoidHom n R)
    additiveCommutators_le_trace_comap

end Matrix
end
