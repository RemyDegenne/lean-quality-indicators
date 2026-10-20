@[expose] public section

open CategoryTheory AlgebraicTopology Limits Metric

open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace SphereOddDegree

variable (n : ℕ)

/-- The equatorial band `Sⁿ⁺¹ \ {north, south}` is homotopy equivalent to `Sⁿ`. -/
def sphereBandHomotopyEquiv : ContinuousMap.HomotopyEquiv (sphereBand n) (Sphere n) where
  toFun := bandToSphere n
  invFun := sphereToBand n
  left_inv := ⟨bandHomotopy n⟩
  right_inv := bandToSphere_comp_sphereToBand n ▸ ContinuousMap.Homotopic.refl _

end SphereOddDegree
end
end
