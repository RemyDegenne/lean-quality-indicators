@[expose] public section

universe u v w uR uτ uσ uL uK

namespace MvPolynomial

theorem surjective_fractionRing_map_rename_iff
    {R : Type uR} [CommRing R] [IsDomain R]
    {τ : Type uτ} {σ : Type uσ}
    {L : Type uL} [CommRing L] [Algebra (MvPolynomial τ R) L]
    [IsFractionRing (MvPolynomial τ R) L]
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K]
    (ρ : τ → σ) (hρ : Function.Injective ρ) :
    Function.Surjective
      (IsFractionRing.map
        (A := MvPolynomial τ R) (B := MvPolynomial σ R)
        (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
        (rename_injective ρ hρ)) ↔ Function.Surjective ρ := by
  classical
  constructor
  · intro h i
    exact (X_mem_range_fractionRing_map_rename_iff
      (R := R) (L := L) (K := K) ρ hρ i).mp
      (h (algebraMap (MvPolynomial σ R) K (X i)))
  · intro honto
    let e : τ ≃ σ := Equiv.ofBijective ρ ⟨hρ, honto⟩
    let ePoly : MvPolynomial τ R ≃+* MvPolynomial σ R :=
      (renameEquiv R e).toRingEquiv
    let eFrac : L ≃+* K :=
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := K) ePoly
    have hmap :
        IsFractionRing.map
          (A := MvPolynomial τ R) (B := MvPolynomial σ R)
          (K := L) (L := K) (j := (rename (R := R) ρ).toRingHom)
          (rename_injective ρ hρ) = eFrac.toRingHom :=
      IsLocalization.map_unique (S := L) (Q := K)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
          (rename (R := R) ρ).toRingHom (rename_injective ρ hρ))
        eFrac.toRingHom fun p =>
          IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := L) (L := K) ePoly p
    rw [hmap]
    exact eFrac.surjective

end MvPolynomial
end
