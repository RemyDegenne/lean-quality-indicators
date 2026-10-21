namespace OAI

noncomputable section

namespace VelocityDetection.RoutingArray

open scoped BigOperators Topology ContDiff

open Set Function Filter

open Set Function Filter MeasureTheory

open scoped Topology BigOperators ContDiff

open scoped Topology ContDiff BigOperators

open scoped Topology ContDiff ZeroAtInfty

open scoped Topology ContDiff ZeroAtInfty BigOperators

open scoped Topology

open scoped Topology ContDiff BigOperators ZeroAtInfty

open Expanding MovingCutoff SmoothProfiles SpatialCalculus

variable (A : RoutingData) (ν : ℝ) (tr : Trace A)

theorem runPath_plateau (hν : 0 < ν) (n : ℕ) (h : tr.stopped n = false) {t : ℝ}
    (ht : t ∈ Icc (startTime ν A.K A.D n) (startTime ν A.K A.D (n + 1)))
    (X : Coord 2) (hX : ∀ i, |X i - runPath A ν tr n t i| ≤ radius ν A.K A.D n) :
    field A ν t X = deriv (runPath A ν tr n) t := by
  rw [runPath_eq_installed A ν tr n h] at hX ⊢
  exact field_plateau A ν hν n (tr.instruction n h) ht X hX

end VelocityDetection.RoutingArray
end
end OAI
