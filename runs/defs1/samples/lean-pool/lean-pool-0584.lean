@[expose] public section

open MvPolynomial

namespace BannaiBannaiStanton

section Polynomials

variable {R : Type*} [CommRing R]

/-- The squared-distance polynomial expressed from a fixed reference point. -/
noncomputable def distPolyFrom {d : ℕ}
 (y : EuclideanSpace R (Fin d)) : MvPolynomial (Fin d) R :=
  ∑ i : Fin d, (X i - C (y i))^2

end Polynomials
end BannaiBannaiStanton
end
