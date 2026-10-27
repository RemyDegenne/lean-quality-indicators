namespace P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField

set_option autoImplicit false

p2m_open

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry

namespace RosenlichtL3

p2m_open

section Chart

variable (k : Type u) [Field k] (d : ℕ)

variable {k d}

variable {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))

abbrev algU (U : P.Opens) : Algebra k Γ(P, U) := (show k →+* Γ(P, U) from (φk p U).hom).toAlgebra

end Chart
end RosenlichtL3
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_exists_isProper_ringKrullDim_stalk_eq_one_of_valuationSubring_functionField
