@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

namespace Ring

universe v w z

variable (S : Type v) (A : Type w) (C : Type z)
  [CommRing S] [CommRing A] [CommRing C]
  [Algebra S A] [Algebra S C]

variable (f g : A →ₐ[S] C)

local instance invariantRingAlgebra : Algebra (invariantRing S A C f g) C :=
  (f.comp (invariantRing S A C f g).val).toRingHom.toAlgebra

/-- The first map, regarded as a morphism over the invariant ring. -/
def fst : A →ₐ[invariantRing S A C f g] C :=
  AlgHom.mk' f.toRingHom (fun b x ↦ by
    change f (b.1 * x) = f b.1 * f x
    rw [map_mul])

end Ring
end AlgebraicGeometry.AffineRelationQuotient
end
end
