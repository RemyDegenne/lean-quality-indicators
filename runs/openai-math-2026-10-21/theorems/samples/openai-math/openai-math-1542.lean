namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section

namespace Ostmann.Arithmetic.HistoryBulkPriorGrid

open Construction PrimeProgression PrimeCellReplacement LogCellPartition

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem bulkPrimeUnit_coe (L : ℝ) (M : ℕ) [NeZero M]
    (hsize : (M : ℝ) < Real.exp (bulkLogLower L)) (p : ℕ)
    (hp : p ∈ bulkClosedSupport L) :
    (bulkPrimeUnit L M hsize p hp : ZMod M) = p := ZMod.coe_unitOfCoprime _ _

end Ostmann.Arithmetic.HistoryBulkPriorGrid
end
end OAI
