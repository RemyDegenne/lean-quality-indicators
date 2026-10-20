open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable {R : Type u} [CommRing R]

@[simp] theorem endpointBasis_repr_X (n : ℕ) (hn : 1 ≤ n)
    (i : Fin n) (hi : 0 < i.val) :
    (@Module.Basis.repr (Fin n) (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _
      (@Algebra.toModule (MvPolynomial (Fin 2) R)
        (Source R n ⧸ hankelIdeal R n) _ _
        (endpointMap (R := R) n).toAlgebra) (endpointBasis R n hn))
        (Ideal.Quotient.mk (hankelIdeal R n) (X i.castSucc)) =
      Finsupp.single i 1 := by
  let : Module (MvPolynomial (Fin 2) R) (Source R n ⧸ hankelIdeal R n) :=
    @Algebra.toModule (MvPolynomial (Fin 2) R)
      (Source R n ⧸ hankelIdeal R n) _ _ (endpointMap (R := R) n).toAlgebra
  simpa only [endpointBasis_apply_of_pos (R := R) n hn i hi] using
    (endpointBasis R n hn).repr_self i

end
end
end ToricIdeals.RationalNormalCurve
