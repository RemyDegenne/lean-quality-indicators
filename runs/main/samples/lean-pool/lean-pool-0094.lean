@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000OrbitalBasis

open scoped BigOperators

open scoped Matrix

open Distributed2Coloring.LowerBound.Correlation

open Distributed2Coloring.LowerBound.N1000000Data

open Distributed2Coloring.LowerBound.N1000000PairTransitivity

open Distributed2Coloring.LowerBound.N1000000StructureConstants

open Distributed2Coloring.LowerBound.N1000000Witness

theorem baseTuple_injective : Function.Injective baseTuple := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [baseTuple] at hij <;> cases hij <;> rfl

end N1000000OrbitalBasis
end Distributed2Coloring.LowerBound
end
