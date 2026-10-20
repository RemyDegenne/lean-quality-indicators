namespace P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj

open scoped MatrixGroups

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace W1GLB

open UpperHalfPlane IntermediateField HahnSeries

open scoped ModularForm

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

p2m_reactivate

section Gen

variable (hqM' : ¬ q ∣ M') (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') (ζ : Idx q)

theorem sum_exp_smul_eq {k : ℤ} (s : ℕ) (h : ℕ → ModularForm (Γ q M') k) :
    (∑ j ∈ Finset.range q, Complex.exp (2 * Real.pi * Complex.I * ((s * j : ℕ) : ℂ) / q) •
        (⇑(h j) : ℍ → ℂ)) =
      ∑ j ∈ Finset.range q, (eq q ^ s) ^ j • (⇑(h j) : ℍ → ℂ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← pow_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end Gen
end W1GLB
end
end P2MW.S_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
