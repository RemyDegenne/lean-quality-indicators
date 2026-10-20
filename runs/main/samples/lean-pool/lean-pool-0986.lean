@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology

open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset

namespace NavierStokes.OutgoingProfile

namespace Profile

theorem renormalized_integrable (F : Profile) (eta : ℝ) :
    IntegrableOn (fun X => F.H (X, eta) - F.powerH X) (Ioi 0) :=
  ReleaseMoments.ResetWitness.renormalized_radial_integrable F.reset eta

end Profile
end NavierStokes.OutgoingProfile
end
end
