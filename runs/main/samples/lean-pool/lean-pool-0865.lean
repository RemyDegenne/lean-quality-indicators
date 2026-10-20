public noncomputable section

namespace ConwayRefinement.Standalone.HahnPolynomial

universe u

namespace IsPolynomialRing

theorem of_polynomiality (K : Type u) [Field K] :
    HahnPolynomial.IsPolynomialRing K := by
  intro hK
  let := hK
  obtain ⟨ι, weight, generators, hminimal, ⟨lifts⟩⟩ :=
    Berarducci.exists_isMinimalSystem_and_generatorLifts K
  let ringEquiv : MvPolynomial ι (FiniteSupport K) ≃+* Series K :=
    (MvPolynomial.mapEquiv ι (finiteSupportEquiv K)).trans
      ((Berarducci.polynomialRingEquiv hminimal lifts).toRingEquiv.trans
        (seriesEquiv K).symm)
  let algEquiv : MvPolynomial ι (FiniteSupport K) ≃ₐ[FiniteSupport K] Series K :=
    AlgEquiv.ofRingEquiv (f := ringEquiv) fun x ↦ by
      change ringEquiv (MvPolynomial.C x) = (x : Series K)
      simp only [ringEquiv, RingEquiv.trans_apply, MvPolynomial.mapEquiv_apply,
        MvPolynomial.map_C]
      change (seriesEquiv K).symm
        (Berarducci.polynomialRingEquiv hminimal lifts
          (MvPolynomial.C (finiteSupportEquiv K x))) = (x : Series K)
      rw [Berarducci.polynomialRingEquiv_apply, Berarducci.evalAtLifts_C]
      rfl
  exact ⟨ι, ⟨algEquiv⟩⟩

end IsPolynomialRing
end ConwayRefinement.Standalone.HahnPolynomial
end
