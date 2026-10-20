public section

open scoped TensorProduct

namespace TauCeti.ConstantGroup

section Universal

variable (R : Type*) [CommRing R] (H : Type*) [Semiring H] [Bialgebra R H] (A : Type*) [Monoid A]
  [Finite A]

/-- **Universal property of the constant monoid.** Bialgebra homomorphisms
`H →ₐc[R] coordinateRing R A` correspond to monoid homomorphisms from `A` to the `R`-points
`WithConv (H →ₐ[R] R)` of `H`; a homomorphism `g` goes to `a ↦ eval a ∘ g`. When `H` is
commutative, these are the homomorphisms of monoid schemes `A_R → Spec H` from the constant
monoid, and `eval a ∘ g` is the image of the point `a` of `A_R`. -/
noncomputable def bialgHomEquiv :
    (H →ₐc[R] coordinateRing R A) ≃ (A →* WithConv (H →ₐ[R] R)) :=
  Equiv.ofBijective _ (mapDomain_comp_bijective (pi_toPoints_bijective R A))

end Universal
end TauCeti.ConstantGroup
end
