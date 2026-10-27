@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

/-- A coordinate class in the quotient. -/
def coordinate (i : Fin 4) : CoordinateRing A := quotientMap A (MvPolynomial.X i)

end SplitQuadric
end
end
