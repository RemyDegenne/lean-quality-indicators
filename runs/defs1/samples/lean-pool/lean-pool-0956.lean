@[expose] public section

namespace NRR

open scoped BigOperators

variable {p : Nat}

namespace FoxNeuwirthOrderComplex

namespace MaximalFlagCode

/-- Bars already removed before stage `j`. -/
def removedBefore (z : Code p) (j : Fin p) : Finset (Fin (p - 1)) :=
  Finset.univ.filter fun r => (z.removal.symm r).1 < j.1

end MaximalFlagCode
end FoxNeuwirthOrderComplex
end NRR
end
