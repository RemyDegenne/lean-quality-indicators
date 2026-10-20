namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine

attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false

namespace P2mStrictOfLine

open Module

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
  (b : Basis (Fin 2) A V)

variable {b}

theorem zc_eq_of_sub_smul_mem {f : V →ₗ[A] V} {a : A} (h : ∀ v : V, f v - a • v ∈ A ∙ b 0) :
    zc b f = a := by
  have h1 := repr_one_eq_zero_of_mem b (h (b 1))
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_b1_one, smul_eq_mul,
    mul_one, sub_eq_zero] at h1
  exact h1

end P2mStrictOfLine
end P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
