public section

namespace Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem moduleFinite_quotient_of_radical (I : Ideal A) (hI : I.radical.FG)
    [Module.Finite R (A ⧸ I.radical)] : Module.Finite R (A ⧸ I) := by
  apply Module.finite_of_surjective_of_ker_le_nilradical
    (Ideal.Quotient.factorₐ R I.le_radical) (Ideal.Quotient.factor_surjective I.le_radical)
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.coe_factorₐ, Ideal.Quotient.factor_ker]
    exact (Ideal.map_radical_le (f := Ideal.Quotient.mk I)).trans
      (by rw [Ideal.map_quotient_self]; rfl)
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.coe_factorₐ, Ideal.Quotient.factor_ker]
    exact hI.map _

end Ideal
end
