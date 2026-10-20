@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

open scoped TensorProduct

@[simp]
theorem quotientHomogeneousBaseChangeEquiv_symm_basis
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (n d : ℕ) (i : Fin (n * d + 1)) :
    (quotientHomogeneousBaseChangeEquiv R S n d).symm
        (quotientHomogeneousBasis S n d i) =
      (1 : S) ⊗ₜ[R] quotientHomogeneousBasis R n d i := by
  apply (quotientHomogeneousBaseChangeEquiv R S n d).injective
  rw [LinearEquiv.apply_symm_apply,
    quotientHomogeneousBaseChangeEquiv_tmul_basis, one_smul]

end
end ToricIdeals.RationalNormalCurve
end
