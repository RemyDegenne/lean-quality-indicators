@[expose] public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

variable (K : Type u) [CommRing K] {σ : Type v} (S : Set σ)

def localizedCoordinateForwardAway (f : MvPolynomial σ K) :
    Localization.Away f →ₐ[K] Localization.Away (eraseCoordinates K S f) :=
  IsLocalization.Away.liftAlgHom f (localizedCoordinateForwardBase_isUnit K S f)

end MvPolynomial
end
end
