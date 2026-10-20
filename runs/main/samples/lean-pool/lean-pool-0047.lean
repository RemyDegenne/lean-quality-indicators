@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingProfile (Profile)

open NavierStokes.OutgoingDilation (switchRadius patchRadius patchRatio compensationPatch
    shapedPatchAmplitude)

namespace NavierStokes.HeatedOutgoing

theorem E_times_U (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (eta X : ℝ)
    (hXR : 0 < XR) (hX : 0 < X) :
    E F XR c (X, eta) * U F XR (X, eta) = OutgoingDilation.E F XR (X, eta) * U F XR (X, eta) := by
  have hp : patchIncrement F XR c (X, eta) * U F XR (X, eta) = 0 := by
    rw [patchIncrement, mul_assoc]
    change shapedPatchAmplitude F eta *
      (TerminalCompensation.correction compensationPatch (c eta) (X / patchRadius F XR) *
        OutgoingDilation.U F XR (X, eta)) = 0
    rw [OutgoingDilation.correction_times_U_zero F XR eta X hXR, mul_zero]
  rw [E, add_mul, heatE_times_U F XR eta X hXR hX, hp, add_zero]

end NavierStokes.HeatedOutgoing
end
end
