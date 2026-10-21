namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open MeasureTheory Filter Set

open scoped Topology

open MeasureTheory ProbabilityTheory Filter Set

namespace SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set

open scoped Topology NNReal BigOperators

variable {ι : Type*}

@[simp] theorem signedClockSteps_zero (as : List PositiveMass) (q r : ℕ → ι → ℝ) :
    affineSteps (signedClockSteps as q r) 0 =
      diagonalBoundarySteps as (q 0) (fun j => q (j+1)) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [signedClockSteps,affineSteps_cons,Pi.sub_apply,zero_mul,add_zero,ih,
      diagonalBoundarySteps]

end SKFluctuations.Hierarchy
end
end OAI
