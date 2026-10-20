@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

/-- The quotient-variable classes form a coefficient-ring basis of the
augmentation kernel modulo its square in the full Hankel quotient.
Scalars use the canonical coefficient algebra action, for every commutative
ring and every degree, including degree zero. -/
noncomputable def quotientAugmentationCotangentBasis (R : Type u) [CommRing R] (n : ℕ) :
    Module.Basis (Fin (n + 1)) R
      (RingHom.ker (quotientAugmentation R n).toRingHom).Cotangent := by
  exact (MvPolynomial.idealOfVarsCotangentBasis (Fin (n + 1)) R).map
    (LinearEquiv.ofBijective
      (Ideal.mapCotangent (MvPolynomial.idealOfVars (Fin (n + 1)) R)
        (RingHom.ker (quotientAugmentation R n).toRingHom)
        (Ideal.Quotient.mkₐ R (hankelIdeal R n))
        (quotientAugmentation_comap_mk R n).ge)
      (quotientAugmentation_mapCotangent_bijective R n))

end ToricIdeals.RationalNormalCurve
end
