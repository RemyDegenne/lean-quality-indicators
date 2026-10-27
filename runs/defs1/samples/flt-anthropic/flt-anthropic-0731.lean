namespace P2MW.S_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace CuspCountX0NBar

local notation "Kb" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N]

variable {N}

variable (N) in

def labels : Finset (Σ _ : ℕ, ℕ) :=
  N.divisors.sigma fun a =>
    {b ∈ Finset.range (Nat.gcd a (N / a)) | (Nat.gcd a (N / a)).Coprime b}

end CuspCountX0NBar
end P2MW.S_ModularCurve_card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg
