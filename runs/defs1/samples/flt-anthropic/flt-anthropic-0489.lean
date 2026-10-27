set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace ModularCurve

namespace TwoChart

variable (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K]

variable {A K}

variable (A K)

variable (j : K) [Fact (j ≠ 0)]

def jInvChartInf : chartAlgInf A K j := ⟨(j)⁻¹, subset_chartAlg A K _ rfl⟩

end TwoChart
end ModularCurve
end
