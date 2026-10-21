namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace Cavity

theorem restHamiltonian_eq (beta : ℝ) {n : ℕ} (hn : 0 < n) (g : Disorder n) (σ : Spin n) :
    restHamiltonian beta n g σ = hamiltonian (restBeta beta n) n g σ := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hn))
  unfold restHamiltonian hamiltonian restBeta
  congr 1
  field_simp

end Cavity
end SKFluctuations
end
end OAI
