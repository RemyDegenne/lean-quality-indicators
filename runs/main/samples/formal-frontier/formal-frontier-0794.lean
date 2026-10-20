set_option warningAsError true

@[expose] public section

namespace MonomialOrder

open MvPolynomial

variable {σ ι R : Type*} [CommRing R]

theorem linearDivision_remainder_coeffsIn (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ R) (hb : ∀ i, IsUnit (m.leadingCoeff (b i)))
    (J : Ideal R) (p : MvPolynomial σ R)
    (hp : p ∈ coeffsIn σ (J : Submodule R R)) :
    linearDivisionRemainder m b hb p ∈ coeffsIn σ (J : Submodule R R) :=
  linearMap_preserves_coeffsIn J (linearDivisionRemainder m b hb) p hp

end MonomialOrder
end
