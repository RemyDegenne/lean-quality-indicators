@[expose] public section

open Finset Hypergraph

namespace Nibble

namespace LEUnif

variable {X : Type} [DecidableEq X]

variable {r m : ℕ} {T : Finset X} {i : Fin (r - #T) → Fin m}

lemma sum_col_two (hm : 0 < m) (x : ℝ) {d : ℕ} {j₀ j₁ : Fin d} (hj : j₀ ≠ j₁) (e e' : Fin m) :
    ∑ f : (Fin d → Fin m), (if f j₀ = e ∧ f j₁ = e' then x / (m : ℝ) ^ d else 0)
      = x / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 2 ≤ d := by
    by_contra hlt
    have h0 := j₀.isLt
    have h1 := j₁.isLt
    have : (j₀ : ℕ) = (j₁ : ℕ) := by omega
    exact hj (Fin.ext this)
  rw [SlackR.sum_ite_at2 d m hj e e' (x / (m : ℝ) ^ d), div_mul_eq_mul_div,
    mul_pow_sub_two_div _ _ hm' d hd]

end LEUnif
end Nibble
end
