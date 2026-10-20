namespace P2MW.S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace Ws25K7fibaF

theorem alg_nn {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (n : ℕ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : a₁ < 0) (hq : q < 0) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) ^ n * (-((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ)) - (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ) - (a : ℂ) * (a₂ : ℂ) * ((((a₂ * q)⁻¹) : ℝ) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + n) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * (-((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 + (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ))) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + n)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  have hne : ∀ {x : ℝ}, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun hx => Complex.ofReal_ne_zero.2 hx.ne'
  have ha₁' : a₁ ≠ 0 := ha₁.ne
  have hq' : q ≠ 0 := hq.ne
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁'

  have hdw : ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹) = ArchR.diagOne (a * |(a₁ / a₂)| * p / q) := by
    congr 1; rw [abs_div, abs_of_pos ha₂]; field_simp
  rw [hdw, show -a₁ / a₂ = -(a₁ / a₂) by ring]
  have g1 : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) =
      Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) * Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) := by
    rw [← Real.exp_add]; congr 1
    rw [div_pow, ← sq_abs a₁]; field_simp; ring
  have g2 : Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) := by
    congr 1; rw [← sq_abs a₁]; field_simp
  have g3 : Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) := by
    congr 1; field_simp
  rw [g1, g2, g3]
  rw [show (2 * s - cP - P₂.centralExponent + n : ℂ) = (s - 1 / 2) + (s - 1 / 2) - cP - P₂.centralExponent + 1 + n by ring,
    show (s - 5 / 2 - cP - P₂.centralExponent : ℂ) = (s - 1 / 2) - 2 - cP - P₂.centralExponent by ring]
  set e₀ : ℂ := s - 1 / 2 with he₀
  obtain ⟨A, hA, rfl⟩ : ∃ A : ℝ, 0 < A ∧ a₁ = -A := ⟨-a₁, neg_pos.2 ha₁, by ring⟩
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℝ, 0 < Q ∧ q = -Q := ⟨-q, neg_pos.2 hq, by ring⟩
  have z1 := hne hA; have z2 := hne ha₂; have z3 := hne hQ; have z4 := hne hp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have n1 := Ws23K7pt.pos_cpow_ne_zero hA e₀; have n2 := Ws23K7pt.pos_cpow_ne_zero ha₂ e₀
  have n3 := Ws23K7pt.pos_cpow_ne_zero hA u₀; have n4 := Ws23K7pt.pos_cpow_ne_zero ha₂ u₀
  have n5 := Ws23K7pt.pos_cpow_ne_zero hQ u₀; have n6 := Ws23K7pt.pos_cpow_ne_zero hp u₀
  have n7 := Ws23K7pt.pos_cpow_ne_zero hA cP; have n8 := Ws23K7pt.pos_cpow_ne_zero ha₂ cP
  have n9 := Ws23K7pt.pos_cpow_ne_zero hA P₂.centralExponent; have n10 := Ws23K7pt.pos_cpow_ne_zero ha₂ P₂.centralExponent
  have n11 := Ws23K7pt.pos_cpow_ne_zero hp P₂.centralExponent
  simp only [neg_mul, mul_neg, neg_neg, inv_neg, abs_neg, neg_div, div_neg, mul_inv, inv_inv, even_two, Even.neg_pow,
    abs_mul, abs_inv, abs_div, abs_of_pos hA, abs_of_pos ha₂, abs_of_pos hQ, abs_of_pos hp]
  simp (disch := positivity) only [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos, ArchR.centralChar,
    Complex.cpow_zero, mul_one, one_mul, neg_neg, Ws25Kit.negone_pow_val]
  simp (disch := positivity) only [mul_cpow_pos, inv_cpow_pos, div_cpow_pos]
  simp only [Complex.cpow_add _ _ z1, Complex.cpow_add _ _ z2, Complex.cpow_add _ _ z3, Complex.cpow_add _ _ z4,
    Complex.cpow_sub _ _ z1, Complex.cpow_sub _ _ z2, Complex.cpow_sub _ _ z3, Complex.cpow_sub _ _ z4,
    Complex.cpow_one, Complex.cpow_ofNat, Complex.cpow_natCast]
  rcases Ws23K7pt.zmod2_cases a₀ with rfl | rfl <;> rcases Ws23K7pt.zmod2_cases sP with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one, zpow_zero, zpow_one] <;>
    (push_cast; field_simp; try ring)

end Ws25K7fibaF
end P2MW.S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_conjBlock
