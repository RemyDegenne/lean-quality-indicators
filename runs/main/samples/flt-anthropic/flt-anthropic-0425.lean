namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mem_toricPts_mul_nsmul_eq

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace E2H4

section Characters

variable (S : Type) [CommRing S] {L : Type} [Field L] [Algebra S L] {t m : ℕ}

variable [NeZero m] {ζ : L} (hζ : ζ ^ m = 1)

include hζ

theorem chi_apply (a v : Fin t → ZMod m) : chi hζ a (Multiplicative.ofAdd v) = ζ ^ (dot a v).val := rfl

end Characters
end E2H4
end
end P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_mem_toricPts_mul_nsmul_eq
