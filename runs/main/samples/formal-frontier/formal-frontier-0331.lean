open MvPolynomial

namespace ToricIdeals.RationalNormalCurve

noncomputable section

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem hankelIdeal_isPrime_iff (R : Type u) [CommRing R] (n : ℕ) :
    (hankelIdeal R n).IsPrime ↔ IsDomain R := by
  constructor
  · intro hprime
    let : (hankelIdeal R n).IsPrime := hprime
    have hcomap : (hankelIdeal R n).comap
        (MvPolynomial.C : R →+* Source R n) = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro r hr
      change (MvPolynomial.C r : Source R n) ∈ hankelIdeal R n at hr
      have hzero := hankelIdeal_le_ker R n hr
      change rncMap R n (MvPolynomial.C r) = 0 at hzero
      have hconstant : rncMap R n (MvPolynomial.C r) =
          (MvPolynomial.C r : Target R) := by
        rw [rncMap, AddMonoidAlgebra.mapDomainRingHom_apply]
        change AddMonoidAlgebra.mapDomain (rncExponent n)
            (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
        rw [AddMonoidAlgebra.mapDomain_single, map_zero]
      rw [hconstant] at hzero
      exact Ideal.mem_bot.mpr (MvPolynomial.C_eq_zero.mp hzero)
    let : (⊥ : Ideal R).IsPrime := by
      rw [← hcomap]
      exact Ideal.comap_isPrime
        (MvPolynomial.C : R →+* Source R n) (hankelIdeal R n)
    exact IsDomain.of_bot_isPrime R
  · intro hdomain
    let : IsDomain R := hdomain
    cases n with
    | zero =>
      rw [hankelIdeal_zero]
      infer_instance
    | succ n =>
      exact hankelIdeal_isPrime R (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

end
end
end ToricIdeals.RationalNormalCurve
