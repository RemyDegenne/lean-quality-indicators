@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The normalized interpolating vector as a point of the twice-punctured circle;
its nonzero second coordinate excludes both removed poles. -/
def circlePunctureIntersectionRadialPoint
    (t : unitInterval) (p : circlePunctureIntersection) :
    circlePunctureIntersection :=
  ⟨⟨circlePunctureIntersectionRadialVector t p,
      mem_sphere_zero_iff_norm.mpr
        (circlePunctureIntersectionRadialVector_norm t p)⟩, by
    constructor <;> intro h
    · have := congrArg (fun q : Metric.sphere (0 : E2) 1 => (q.1 : E2) 1) h
      exact circlePunctureIntersectionRadialVector_second_ne_zero t p (by
        simpa [eastPoint, eastVector] using this)
    · have := congrArg (fun q : Metric.sphere (0 : E2) 1 => (q.1 : E2) 1) h
      exact circlePunctureIntersectionRadialVector_second_ne_zero t p (by
        simpa [westPoint, eastPoint, eastVector] using this)⟩

end SphereTopology
end
end
