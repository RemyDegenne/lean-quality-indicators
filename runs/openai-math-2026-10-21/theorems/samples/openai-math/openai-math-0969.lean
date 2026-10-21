namespace OAI

noncomputable section

open Bundle Set Filter

open scoped Manifold Bundle Topology BoundedContinuousFunction

open scoped Topology

open Set Filter

namespace QuotientLift

open scoped OnePoint Manifold

local instance branchedSphereDecidableEq : DecidableEq Sphere := Classical.decEq Sphere

@[simp] lemma zero_affine (z : ℂ) : (0 : SphereTangentSection).affine z = 0 := by
  have h : (0 : SphereTangentSection) = polynomialSection 0 := by
    apply coefficients_injective
    simp
  rw [h]
  simp [polynomialSection]

end QuotientLift
end
end OAI
