@[expose] public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

variable (K : Type u) [CommRing K] {σ : Type v} (S : Set σ)

/-- Evaluation at zero on the variables outside `S`, retaining the variables in `S`.
This is mathlib's `MvPolynomial.killCompl` for the inclusion `S ↪ σ`. -/
def eraseCoordinates : MvPolynomial σ K →ₐ[K] MvPolynomial S K :=
  killCompl (f := ((↑) : S → σ)) Subtype.val_injective

end MvPolynomial
end
end
