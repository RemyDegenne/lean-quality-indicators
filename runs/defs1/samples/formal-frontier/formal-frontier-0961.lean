@[expose] public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

variable (K : Type u) [CommRing K] {σ : Type v} (S : Set σ)

def localizedCoordinateInverseBase (f : MvPolynomial σ K) :
    MvPolynomial S K →ₐ[K] (Localization.Away f ⧸ localizedCoordinateIdeal K S f) :=
  aeval (fun i : S => (Ideal.Quotient.mkₐ K (localizedCoordinateIdeal K S f))
    (algebraMap (MvPolynomial σ K) (Localization.Away f) (X i.1)))

end MvPolynomial
end
end
