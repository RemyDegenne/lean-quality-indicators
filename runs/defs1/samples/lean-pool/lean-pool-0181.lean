@[expose] public section

namespace O3

/-- The upper-model guard between the estimate query and the next accelerated iterate. -/
noncomputable def euclideanEstimateGuard {d : ℕ}
    (P : AdmissibleInstance d 2) (M : ℝ) (k : ℕ) : GuardCheck :=
  let atY := euclideanEstimateObservation P M k
  let xNext := (euclideanEstimateState P M (k + 1)).accelerated
  let atX := P.oracle.observe xNext
  upperModelGuard atY.value atX.value
    (pairing atY.gradient (xNext - atY.point))
    ((lpNorm 2 (xNext - atY.point)) ^ (2 : ℕ)) M

end O3
end
