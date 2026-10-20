@[expose] public section

set_option warningAsError true

noncomputable section

namespace MvPolynomial

universe u v

variable (K : Type u) [CommRing K] {σ : Type v} (S : Set σ)

theorem localizedCoordinateInverseBase_isUnit (f : MvPolynomial σ K) :
    IsUnit (localizedCoordinateInverseBase K S f (eraseCoordinates K S f)) := by
  have h := AlgHom.congr_fun (localizedCoordinateInverseBase_erase K S f) f
  simp only [AlgHom.comp_apply] at h
  rw [h]
  exact IsUnit.map (Ideal.Quotient.mkₐ K (localizedCoordinateIdeal K S f))
    (IsLocalization.Away.algebraMap_isUnit f)

end MvPolynomial
end
end
