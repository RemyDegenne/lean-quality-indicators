@[expose] public section

namespace NRR

open scoped BigOperators Matrix

variable {p : Nat}

namespace FoxNeuwirthOrderComplex

namespace ReferenceAffineOrbitCount

open MaximalFlagCode TopFlagSubdivision PrimeOrbitCycle

/-- A maximal simplex is one of the selected reference simplices. -/
def IsSelected
    (hp : Nat.Prime p) (s : Simplex p (p - 1)) : Prop :=
  ∃ sigma : Equiv.Perm (Fin p), s = selectedSimplex hp sigma

end ReferenceAffineOrbitCount
end FoxNeuwirthOrderComplex
end NRR
end
