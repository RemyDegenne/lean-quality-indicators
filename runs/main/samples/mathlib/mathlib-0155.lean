@[expose] public section

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open Complex Set MeasureTheory Function Filter TopologicalSpace

open Mathlib.Tactic (superscriptTerm)

open scoped Real

local syntax:arg term:max noWs superscriptTerm : term

local macro_rules | `($t:term$n:superscript) => `(Fin $n → $t)

theorem torusMap_eq_center_iff {c : ℂⁿ} {R : ℝⁿ} {θ : ℝⁿ} : torusMap c R θ = c ↔ R = 0 := by
  simp [funext_iff, torusMap, exp_ne_zero]

end
end
