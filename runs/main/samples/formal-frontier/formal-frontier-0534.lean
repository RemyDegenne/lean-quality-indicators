@[expose] public section

universe u v

namespace MvPolynomial

theorem isArtinianRing_iff {σ : Type u} {R : Type v} [CommSemiring R] :
    IsArtinianRing (MvPolynomial σ R) ↔ IsArtinianRing R ∧ (IsEmpty σ ∨ Subsingleton R) := by
  constructor
  · intro h
    let : IsArtinianRing (MvPolynomial σ R) := h
    have hsurj : Function.Surjective (constantCoeff : MvPolynomial σ R →+* R) :=
      fun r ↦ ⟨C r, constantCoeff_C σ r⟩
    refine ⟨hsurj.isArtinianRing, ?_⟩
    rcases isEmpty_or_nonempty σ with hσ | hσ
    · exact Or.inl hσ
    · right
      let i : σ := Classical.choice hσ
      -- A regular variable is a unit; its constant coefficient then makes zero a unit.
      have hx : IsUnit (X i : MvPolynomial σ R) :=
        IsArtinianRing.isUnit_iff_isRegular.mpr isRegular_X
      have hz : IsUnit (0 : R) := by
        simpa only [constantCoeff_X] using
          hx.map (constantCoeff : MvPolynomial σ R →+* R)
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hz)
  · rintro ⟨hR, hσ | hRsub⟩
    · let : IsArtinianRing R := hR
      let : IsEmpty σ := hσ
      exact (isEmptyAlgEquiv R σ).toRingEquiv.symm.isArtinianRing
    · let : Subsingleton R := hRsub
      exact isArtinian_of_finite (R := MvPolynomial σ R) (M := MvPolynomial σ R)

end MvPolynomial
end
