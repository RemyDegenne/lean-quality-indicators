namespace OAI

noncomputable section

namespace VelocityDetection.MildScalar

open scoped BigOperators Topology ContDiff

open Set Function Filter

open Set Function Filter MeasureTheory

open scoped Topology BigOperators ContDiff

open scoped Topology ContDiff BigOperators

open scoped Topology ContDiff ZeroAtInfty

open scoped Topology ContDiff ZeroAtInfty BigOperators

open scoped Topology

open HeatKernels TailSpace.Jets WeakVolterra

variable {T : ℝ} {a : ℕ} (hT : 0 ≤ T) {ν : ℝ} (hν : 0 < ν)

variable (W : Fin 2 → TimeCurve T a)

theorem continuous_sourceKernel (ν : ℝ) :
    Continuous (fun p : ℝ × ℝ × E a => sourceKernel (a := a) ν p.1 p.2.1 p.2.2) := by
  change Continuous ((fun r : ℝ × E a => heat ν r.1 r.2) ∘
    (fun p : ℝ × ℝ × E a => (p.1, p.2.2)))
  apply Continuous.comp
  · exact continuous_heat_joint (a := a) ν
  · exact continuous_fst.prodMk continuous_snd.snd

end VelocityDetection.MildScalar
end
end OAI
