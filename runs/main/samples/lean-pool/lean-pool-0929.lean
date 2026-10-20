@[expose] public section

namespace NavierStokes.MeanStateRegularity

noncomputable section

open Set Function Filter

open scoped ContDiff Topology

open MeanIncrementBounds CorrectionState LocalSignedRequest

namespace Periodic

variable {U : Set Plane} {f g : Scalar}

theorem band_mul (hf : Periodic U f) (c : ℕ → ℝ) :
    Periodic U (fun n x => c n * f n x) :=
  fun n R s hs Y k => congrArg (fun t : ℝ => c n * t) (hf n R s hs Y k)

end Periodic
end
end NavierStokes.MeanStateRegularity
end
