@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

/-- Subtract `1` from a principal unit and reduce its ideal coordinate modulo `J`.
The square containment kills the product cross term. -/
def principalUnitsToQuotient (I J : Ideal R) (hsq : I ^ 2 ≤ J) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) →*
      Multiplicative (I ⧸ Submodule.comap I.subtype J) where
  toFun u := Multiplicative.ofAdd
    (Submodule.Quotient.mk (⟨(u.1 : R) - 1, (I.mem_stabilizer_quotient_one u.1).mp u.property⟩ : I))
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (1 : R) - 1 ∈ J
    simp
  map_mul' := by
    intro a b
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    rw [← Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).mpr
    change (a.1 : R) * (b.1 : R) - 1 - ((a.1 : R) - 1 + ((b.1 : R) - 1)) ∈ J
    have hcross : ((a.1 : R) - 1) * ((b.1 : R) - 1) ∈ I ^ 2 := by
      rw [Submodule.pow_succ, Submodule.pow_one]
      exact Ideal.mul_mem_mul
        ((I.mem_stabilizer_quotient_one a.1).mp a.property)
        ((I.mem_stabilizer_quotient_one b.1).mp b.property)
    convert hsq hcross using 1
    noncomm_ring

end Ideal
end
