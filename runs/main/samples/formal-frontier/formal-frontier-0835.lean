@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

open scoped TensorProduct

theorem quotientHomogeneousBaseChangeEquiv_tmul
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n d : ℕ) (s : S) (x : quotientHomogeneousSubmodule R n d) :
    (quotientHomogeneousBaseChangeEquiv R S n d (s ⊗ₜ[R] x) :
        Source S n ⧸ hankelIdeal S n) =
      s • Ideal.quotientMap (hankelIdeal S n) (MvPolynomial.map (algebraMap R S))
        ((Ideal.map_le_iff_le_comap).mp (map_hankelIdeal (algebraMap R S) n).le)
        (x : Source R n ⧸ hankelIdeal R n) := by
  have h := LinearMap.congr_fun
    (quotientHomogeneousBaseChangeEquiv_coe R S n d) (s ⊗ₜ[R] x)
  change (quotientHomogeneousBaseChangeEquiv R S n d (s ⊗ₜ[R] x) :
      Source S n ⧸ hankelIdeal S n) =
    quotientBaseChangeAlgEquiv R S n
      (((quotientHomogeneousSubmodule R n d).subtype.baseChange S) (s ⊗ₜ[R] x)) at h
  rw [LinearMap.baseChange_tmul, quotientBaseChangeAlgEquiv_tmul] at h
  exact h

end
end ToricIdeals.RationalNormalCurve
end
