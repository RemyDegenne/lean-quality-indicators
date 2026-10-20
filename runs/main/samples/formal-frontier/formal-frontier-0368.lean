@[expose] public section

universe u v

noncomputable section

theorem IsLocallyNormalRing.pi
    {I : Type*} (S : I → Type*) [∀ i, CommRing (S i)] [Finite I]
    [∀ i, IsLocallyNormalRing (S i)] : IsLocallyNormalRing (∀ i, S i) := by
  constructor
  · intro p
    obtain ⟨i, q, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
    subst p
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsDomain (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isDomain_atPrime q
    exact e.toMulEquiv.isDomain _
  · intro p
    obtain ⟨i, q, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
    subst p
    let e : Localization.AtPrime (q.asIdeal.comap (Pi.evalRingHom S i)) ≃+*
        Localization.AtPrime q.asIdeal :=
      RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
        (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let _ : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
      IsLocallyNormalRing.isIntegrallyClosed_atPrime q
    exact IsIntegrallyClosed.of_equiv e.symm

end
end
