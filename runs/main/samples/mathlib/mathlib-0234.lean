@[expose] public section

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace

open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term

local macro_rules | `($t:term$n:superscript) => `(Fin $n → $t)

variable [NormedSpace ℂ E] {f g : ℂⁿ → E} {c : ℂⁿ} {R : ℝⁿ}

@[inherit_doc torusIntegral]
notation3 "∯ " (...) " in " "T(" c ", " R ")" ", " r:(scoped f => torusIntegral f c R) => r

theorem torusIntegral_radius_zero (hn : n ≠ 0) (f : ℂⁿ → E) (c : ℂⁿ) :
    (∯ x in T(c, 0), f x) = 0 := by
  simp only [torusIntegral, Pi.zero_apply, ofReal_zero, zero_mul, Fin.prod_const,
    zero_pow hn, zero_smul, integral_zero]

end
end
