@[expose] public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

variable (K : Type u) [CommRing K] {σ : Type v} (S : Set σ)

def localizedCoordinateForwardBase (f : MvPolynomial σ K) :
    MvPolynomial σ K →ₐ[K] Localization.Away (eraseCoordinates K S f) :=
  (Algebra.algHom K (MvPolynomial S K) _).comp (eraseCoordinates K S)

end MvPolynomial
end
end
