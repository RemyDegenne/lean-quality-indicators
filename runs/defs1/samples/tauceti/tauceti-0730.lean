public section

noncomputable section

open Metric Set Topology Topology.Homotopy

open scoped unitInterval

namespace TauCeti

section Ball

variable (n : ℕ)

variable {n}

variable (n) in
/-- **The closed unit ball modulo its boundary is the sphere.**  The map from the closed unit ball
of `ℝⁿ` to the unit sphere of `ℝⁿ⁺¹` sending `x` to `(2 √(1 - ‖x‖²) x, 2 ‖x‖² - 1)`, the last
coordinate being the height.  It sends the centre to the south pole, collapses the boundary sphere
to the north pole (`TauCeti.closedBallToSphere_eq_sphereNorthPole_iff`), is injective on the open
ball (`TauCeti.closedBallToSphere_eq_closedBallToSphere_iff`) and is surjective in positive
dimension (`TauCeti.closedBallToSphere_surjective`). -/
def closedBallToSphere :
    C(closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    where
  toFun x := ⟨closedBallToSphereAux x, by
    simpa using norm_closedBallToSphereAux (mem_closedBall_zero_iff.1 x.2)⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp ?_) _
    refine Continuous.finSnoc (continuous_pi fun i ↦ ?_) ?_ <;> fun_prop

end Ball
end TauCeti
end
end
