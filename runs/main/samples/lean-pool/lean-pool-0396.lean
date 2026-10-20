@[expose] public section

noncomputable section

open MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps

namespace StationaryHarmonicMap

theorem weak_radial_cutoff_integrable_of_W12Loc_contDiffBump {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume := by
  rcases ContDiffBump.exists_admissibleRadialCutoff (n := n) f hRout with ⟨M1, hcut⟩
  exact weak_radial_cutoff_integrable_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := 1) (M1 := M1)
    hW hclosedBall_subset hcut

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
end
end
