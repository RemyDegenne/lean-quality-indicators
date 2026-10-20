@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingProfile (Profile)

open NavierStokes.OutgoingDilation (switchRadius patchRadius patchRatio compensationPatch
    shapedPatchAmplitude)

namespace NavierStokes.HeatedOutgoing

theorem CompensationWitness.specification {F : Profile} {XR B C : ℝ}
    (w : CompensationWitness F XR C) (hF : OutgoingProfile.Specification F B) :
    Specification F XR w.coefficients where
  angular_smooth := E_contDiffOn F XR w.radius_pos w.smooth
  axial_smooth := U_contDiffOn F XR w.radius_pos
  momentum_smooth := H_contDiffOn F XR w.radius_pos w.smooth
  pressure_smooth := w.Pi_contDiffOn
  angular_positive := fun eta heta X hX => w.positive eta X heta hX
  axial_unchanged := rfl
  mass_unchanged := M_unchanged F XR
  angular_unchanged := fun eta X => J_unchanged F XR w.coefficients eta X w.radius_pos
  mass_integrable := w.mass_integrable
  angular_integrable := w.angular_integrable
  mass_zero := w.mass_zero
  angular_zero := w.angular_zero
  after_pulse := w.after_pulse
  energy_integrable := w.energy_integrable
  energy_zero := w.energy_zero hF
  renormalized_integrable := w.renormalized_integrable
  renormalized_zero := w.renormalized_zero
  pressure_integrable := w.canonicalKernel_integrable
  pressure_canonical := fun _ _ => rfl
  axis_unchanged := w.axisDatum_eq
  axis_limit := w.Pi_tendsto_axis
  analytic_axis_datum := w.axisDatum_analytic_extension
  before_patch := fun eta heta X hX hp =>
    ⟨E_before_patch F XR w.coefficients eta X w.radius_pos hX hp, w.Pi_before_patch eta X heta hX
        hp⟩
  ideal_prefix := fun eta heta X hX hp => w.ideal_prefix eta X heta hX hp
  switch_overlap := fun eta X hX => E_after_switch F XR w.coefficients eta X w.radius_pos hX
  terminal_heat := fun eta X hX htail => E_eventual_heat F XR w.coefficients eta X w.radius_pos hX
      htail
  patch_disjoint := OutgoingDilation.patch_switch_disjoint F XR w.radius_pos

end NavierStokes.HeatedOutgoing
end
end
