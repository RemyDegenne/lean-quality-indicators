@[expose] public section

namespace NRR

open Geometry

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex

namespace EquivariantPrismVertexParameters

open EquivariantCoordinateHomotopy

open SubdivisionPrismCharts

variable {p : Nat}

/-- Point-coordinate pairs on which prime symmetry acts diagonally. -/
abbrev ScalarSite (hp : Nat.Prime p) (N L : Nat) :=
  GlobalVertex hp N L × Fin p

end EquivariantPrismVertexParameters
end FoxNeuwirthOrderComplex
end NRR
end
