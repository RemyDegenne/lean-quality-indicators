@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

/-- The quotient projection as an `A`-algebra homomorphism. -/
def quotientMap : Polynomial A →ₐ[A] CoordinateRing A :=
  Ideal.Quotient.mkₐ A (relationIdeal A)

end SplitQuadric
end
end
