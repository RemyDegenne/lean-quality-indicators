@[expose] public section

set_option warningAsError true

namespace Polynomial

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The prime ideal of polynomials vanishing at `x`. -/
noncomputable def evalPrime (x : R) : PrimeSpectrum R[X] :=
  ⟨RingHom.ker (evalRingHom x), RingHom.ker_isPrime (evalRingHom x)⟩

end Polynomial
end
