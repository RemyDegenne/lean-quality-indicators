@[expose] public section

noncomputable section

open Homogenization MeasureTheory AVenhance

open AVenhance.Infra.Section4

local instance avInfraSection5ContractsTMaterialSpatialCoefficientNormedAddCommGroup1 :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedAddCommGroup

local instance avInfraSection5ContractsTMaterialSpatialCoefficientNormedSpace2 : NormedSpace ℝ
    (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedSpace

namespace AVenhance.Infra.Section5.Contracts

/-- The all-suborder flow budget `40 n! L^n` used for the quadratic Leibniz estimate. -/
def TMaterialSpatialCoefficient.tMaterialFlowBudget (L : ℝ) (n : ℕ) : ℝ := 40 * (n.factorial : ℝ)
    * L ^ n

end AVenhance.Infra.Section5.Contracts
end
end
