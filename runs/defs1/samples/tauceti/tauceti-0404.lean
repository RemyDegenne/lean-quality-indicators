public section

namespace TauCeti

variable (G A : Type*) [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

namespace CStarAction

variable {G A}

/-- The trivial action, including on the zero algebra. -/
def trivial : CStarAction G A where
  toMonoidHom := 1
  continuous_orbit _ := by simpa using continuous_const

end CStarAction
end TauCeti
end
