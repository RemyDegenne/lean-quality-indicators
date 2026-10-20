@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "derivative_simp" : tactic =>
  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
    derivative_sub, derivative_mul, derivative_sq])

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Affine R} {W : Affine F}

namespace Affine

section slope

variable [DecidableEq F]

omit [DecidableEq F] in
lemma den_duplication_ne_zero_or_num_duplication_ne_zero {x y : F} (h : W.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.nonsingular_iff x y).mp h
  rw [equation_iff x y] at h₁
  by_cases H : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by grind
    contrapose h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose H
    rw [b₂, b₄, b₆] at H
    grobner

end slope
end Affine
end WeierstrassCurve
end
