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

/-- The canonical map from the tensor square over the invariant ring to the
target ring. It sends `x ⊗ₜ y` to `f x * g y`, the swapped-leg orientation
relative to the displayed map in Stacks Project, Proposition 39.23.9
(tag 03BM). -/
def kernelPairComparison :
    _root_.TensorProduct (invariantRing S A C f g) A A
      →ₐ[invariantRing S A C f g] C :=
  Algebra.TensorProduct.lift (fst S A C f g) (snd S A C f g)
    (fun _ _ ↦ Commute.all _ _)

end Ring
end AlgebraicGeometry.AffineRelationQuotient
end
end
