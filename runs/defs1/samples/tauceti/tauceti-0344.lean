public section

open Set Metric Topology

namespace TauCeti

/-- The closed solid torus `D² × S¹`, where `D²` is the closed unit disc of `ℂ`. -/
abbrev SolidTorus : Type := closedBall (0 : ℂ) 1 × Circle

end TauCeti
end
