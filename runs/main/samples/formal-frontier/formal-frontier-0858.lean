open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem quotient_isReduced_iff (R : Type u) [CommRing R] (n : ℕ) :
    IsReduced (Source R n ⧸ hankelIdeal R n) ↔ IsReduced R := by
  constructor
  · intro hquotient
    let : IsReduced (Source R n ⧸ hankelIdeal R n) := hquotient
    have hconstant (r : R) : rncMap R n (C r) = (C r : Target R) := by
      rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
      change AddMonoidAlgebra.mapDomain (rncExponent n)
          (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
      rw [AddMonoidAlgebra.mapDomain_single, map_zero]
    let f : R →+* Source R n ⧸ hankelIdeal R n :=
      (Ideal.Quotient.mk (hankelIdeal R n)).comp (MvPolynomial.C : R →+* Source R n)
    have hf : Function.Injective f := by
      intro a b hab
      have hker := hankelIdeal_le_ker R n (Ideal.Quotient.eq.mp hab)
      change rncMap R n (C a - C b) = 0 at hker
      rw [map_sub, hconstant, hconstant, sub_eq_zero] at hker
      exact MvPolynomial.C_injective (Fin 2) R hker
    exact isReduced_of_injective f hf
  · intro hR
    let : IsReduced R := hR
    cases n with
    | zero =>
      rw [hankelIdeal_zero]
      exact isReduced_of_injective (RingEquiv.quotientBot (Source R 0))
        (RingEquiv.quotientBot (Source R 0)).injective
    | succ n =>
      let e := quotientEquivRange R (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      exact isReduced_of_injective ((rncMap R (n + 1)).range.subtype.comp e.toRingHom)
        ((rncMap R (n + 1)).range.subtype_injective.comp e.injective)

end
end
end ToricIdeals.RationalNormalCurve
