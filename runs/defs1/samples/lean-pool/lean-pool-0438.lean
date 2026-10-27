@[expose] public section

namespace LeanPool.PoincareThreeBody

open MeasureTheory

/-- A resonant Kepler ellipse with an arbitrary inertial orientation phase. -/
noncomputable def orientedResonantEllipsePosition
    (p q : ℕ) (eccentricity orientation time : ℝ) : ActionSpace :=
  positionInRotatingFrame (time - orientation)
    (inertialEllipsePosition (resonantFirstAction p q) eccentricity
      (resonantEccentricAnomaly p q eccentricity time))

end LeanPool.PoincareThreeBody
end
