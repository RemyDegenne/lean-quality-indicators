@[expose] public section

namespace NRR

variable {p d m l : Nat}

namespace FoxNeuwirthOrderComplex

noncomputable section

namespace Realization

/-- Coordinate vector of a vertex. -/
def vertexWeight (c : BarredPermutation p) :
    BarredPermutation p → ℝ :=
  fun d => if d = c then 1 else 0

end Realization
end
end FoxNeuwirthOrderComplex
end NRR
end
