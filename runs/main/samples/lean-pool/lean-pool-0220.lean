@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff

open NavierStokes.ProfileHistories

open NavierStokes.OutgoingProfile

open NavierStokes.NominalProfile (AxisStage Controls SmallDebt)

open NavierStokes.StressActivation

namespace NavierStokes.NominalConeAssembly

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_fields {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.U (chart W.controls.radius p) = F.logU p ∧
    W.profiles.E (chart W.controls.radius p) = HeatSwitchCone.logE F W.controls.radius
        W.heat.coefficients p ∧
    W.profiles.H (chart W.controls.radius p) = Real.sqrt (2 * W.controls.radius) * Real.exp (p.1 /
        2) *
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have he : W.profiles.E (chart W.controls.radius p) =
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p :=
    (W.E_eq_sqrt_f hx).symm.trans (W.heat_agreement hp heta).2.1
  refine ⟨(W.U_outgoing hp).trans (outgoing_U_chart F W.controls.radius_pos p), he, ?_⟩
  have hH : W.profiles.H (chart W.controls.radius p) =
      Real.sqrt (2 * (chart W.controls.radius p).1) * W.profiles.E (chart W.controls.radius p) := by
    dsimp only [Profiles.H, Profiles.E]
    rw [← mul_assoc, Real.mul_self_sqrt (mul_nonneg (by norm_num) hx.le)]
  rw [hH, he]
  exact congrArg (fun z => z * HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p)
    (sqrt_chart W.controls.radius_pos p.1)

end Witness
end NavierStokes.NominalConeAssembly
end
end
