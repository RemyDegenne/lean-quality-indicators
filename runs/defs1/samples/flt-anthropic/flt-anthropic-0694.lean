namespace P2MW.S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent

set_option autoImplicit false

universe u v w

namespace PI0C1

open Algebra

section Core

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Module.Finite k A]

attribute [local instance] Ideal.Quotient.field

scoped instance maximalSpectrum_isMaximal {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal

scoped instance : IsReduced (Ared A) := (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)

noncomputable def piEquiv : Ared A ≃ₐ[k] (∀ I : MaximalSpectrum (Ared A), Fi A I) :=
  haveI : IsArtinianRing (Ared A) := isArtinianRing_Ared k A
  (IsArtinianRing.equivPi (Ared A)).restrictScalars k

end Core
end PI0C1
end P2MW.S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent
