/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Dynamics.Newton
public import Mathlib.Analysis.Normed.Field.Ultra
public import Mathlib.Topology.MetricSpace.Contracting
public import PolynomialRootStability.Ultrametric

/-!
# Quantitative Newton lifting in complete ultrametric fields

Newton iteration is the iteration of Mathlib's `Polynomial.newtonMap`; no additional
sequence object is needed. The field recurrence identifies it with division by the
polynomial derivative. The lifting statement includes nonzero denominators at every
iterate, integrality of iterates, convergence, and quantitative control of the root.

## Implementation notes

The proof restricts the stock Newton map to the closed ball of radius `δ / d`, where
`δ` is the initial error and `d` the initial derivative norm. The derivative norm is
constant there, and Taylor's estimate makes the restricted map a contraction with
constant `δ / d²`. Mathlib's Banach fixed point theorem gives convergence of the
original iterates. This also handles zero initial error and trivially normed fields.

The coefficient bound means integrality in the norm unit ball. No monicity,
characteristic, nontrivial-norm, or norm-one derivative hypothesis is imposed.
This real-valued norm formulation does not address arbitrary higher-rank valuations.

## References

* I. B. Fesenko and S. V. Vostokov, *Local Fields and Their Extensions*, second edition,
  AMS, 2002, Chapter II, §1, Corollary 3, p. 37, and Exercise 1, p. 38.
* Mathlib's `Polynomial.newtonMap`, due to Antoine Chambert-Loir and Oliver Nash.
* Mathlib's Banach fixed point API, due to Rohan Mitta, Kevin Buzzard, Alistair Tucker,
  Johannes Hölzl, and Yury Kudryashov.
* Mathlib's p-adic `hensels_lemma`, following Robert Y. Lewis's formalization and
  Keith Conrad's exposition, for the quantitative p-adic endpoint generalized here.
-/

@[expose] public section

open Filter Function
open scoped Topology

namespace Polynomial

universe u v

section Field

variable {R : Type v} {K : Type u} [CommRing R] [Field K] [Algebra R K]
  (f : R[X]) (a : K)

/-- Over a field, the polynomial Newton map is the usual quotient formula.
As for field division, its value is defined even when the derivative vanishes. -/
theorem newtonMap_apply_eq_sub_div :
    f.newtonMap a = a - f.aeval a / f.derivative.aeval a := by
  simp only [newtonMap_apply, Ring.inverse_eq_inv, div_eq_mul_inv, mul_comm]

end Field

private theorem norm_sub_le_max {K : Type u} [NormedField K] [IsUltrametricDist K]
    (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa only [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

private theorem norm_eq_of_norm_sub_lt {K : Type u} [NormedField K]
    [IsUltrametricDist K] {x y : K} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by
  simpa only [sub_add_cancel, max_eq_right h.le] using
    (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt h))

private theorem norm_eval_sub_eq_of_taylor {K : Type u} [NormedField K]
    [IsUltrametricDist K] {f : K[X]} {x y : K}
    (hTaylor : ‖f.eval x - f.eval y - f.derivative.eval y * (x - y)‖ ≤ ‖x - y‖ ^ 2)
    (hxy : ‖x - y‖ < ‖f.derivative.eval y‖) :
    ‖f.eval x - f.eval y‖ = ‖f.derivative.eval y‖ * ‖x - y‖ := by
  by_cases heq : x = y
  · simp [heq]
  have ht : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  rw [← norm_mul]
  apply norm_eq_of_norm_sub_lt
  rw [norm_mul]
  exact hTaylor.trans_lt (by simpa only [pow_two] using mul_lt_mul_of_pos_right hxy ht)

/-- The analytic argument uses only the derivative and Taylor bounds on the unit ball.
The Newton map is a contraction on the closed ball of radius `δ / d`, with constant
`δ / d²`, where `δ` is the initial error and `d` the initial derivative norm. -/
private theorem exists_root_of_newton_bounds
    {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {f : K[X]} {a₀ : K} (ha₀ : ‖a₀‖ ≤ 1)
    (hD : ‖f.derivative.eval a₀‖ ≤ 1)
    (hLip : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖f.derivative.eval x - f.derivative.eval y‖ ≤ ‖x - y‖)
    (hTaylor : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      ‖f.eval x - f.eval y - f.derivative.eval y * (x - y)‖ ≤ ‖x - y‖ ^ 2)
    (hclose : ‖f.eval a₀‖ < ‖f.derivative.eval a₀‖ ^ 2) :
    ∃ a : K, f.eval a = 0 ∧ ‖a‖ ≤ 1 ∧
      ‖a - a₀‖ = ‖f.eval a₀‖ / ‖f.derivative.eval a₀‖ ∧
      ‖a - a₀‖ < ‖f.derivative.eval a₀‖ ∧
      ‖f.derivative.eval a‖ = ‖f.derivative.eval a₀‖ ∧
      Tendsto (fun n : ℕ => f.newtonMap^[n] a₀) atTop (𝓝 a) ∧
      (∀ n : ℕ, ‖f.newtonMap^[n] a₀‖ ≤ 1 ∧
        f.derivative.eval (f.newtonMap^[n] a₀) ≠ 0 ∧
        ‖f.derivative.eval (f.newtonMap^[n] a₀)‖ = ‖f.derivative.eval a₀‖) ∧
      ∀ b : K, f.eval b = 0 → ‖b - a₀‖ < ‖f.derivative.eval a₀‖ → b = a := by
  let δ := ‖f.eval a₀‖
  let d := ‖f.derivative.eval a₀‖
  let r := δ / d
  have hδ : 0 ≤ δ := norm_nonneg _
  have hd : 0 < d := by
    have hd0 : 0 ≤ d := norm_nonneg _
    have hd2 : 0 < d ^ 2 := hδ.trans_lt hclose
    nlinarith
  have hr : 0 ≤ r := div_nonneg hδ hd.le
  have hrd : r < d := (div_lt_iff₀ hd).2 (by simpa [pow_two] using hclose)
  have hr1 : r ≤ 1 := hrd.le.trans hD
  have hunit : ∀ x : K, ‖x - a₀‖ ≤ r → ‖x‖ ≤ 1 := by
    intro x hx
    calc
      ‖x‖ = ‖(x - a₀) + a₀‖ := by rw [sub_add_cancel]
      _ ≤ max ‖x - a₀‖ ‖a₀‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (hx.trans hr1) ha₀
  -- The derivative has constant, positive norm throughout the small closed ball.
  have hderiv : ∀ x : K, ‖x - a₀‖ ≤ r → ‖f.derivative.eval x‖ = d := by
    intro x hx
    exact norm_eq_of_norm_sub_lt ((hLip x a₀ (hunit x hx) ha₀).trans_lt (hx.trans_lt hrd))
  have hne : ∀ x : K, ‖x - a₀‖ ≤ r → f.derivative.eval x ≠ 0 := by
    intro x hx
    exact norm_pos_iff.mp (by rw [hderiv x hx]; exact hd)
  have heval : ∀ x : K, ‖x - a₀‖ ≤ r → ‖f.eval x‖ ≤ δ := by
    intro x hx
    have hlin := norm_eval_sub_eq_of_taylor (hTaylor x a₀ (hunit x hx) ha₀)
      (hx.trans_lt hrd)
    have hmul : d * r = δ := mul_div_cancel₀ δ hd.ne'
    calc
      ‖f.eval x‖ = ‖(f.eval x - f.eval a₀) + f.eval a₀‖ := by rw [sub_add_cancel]
      _ ≤ max ‖f.eval x - f.eval a₀‖ δ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ δ := max_le (by rw [hlin]; exact (mul_le_mul_of_nonneg_left hx hd.le).trans_eq hmul)
        le_rfl
  have hmap : ∀ x : K, ‖x - a₀‖ ≤ r → ‖f.newtonMap x - a₀‖ ≤ r := by
    intro x hx
    have hstep : ‖f.newtonMap x - x‖ ≤ r := by
      rw [newtonMap_apply_eq_sub_div, coe_aeval_eq_eval,
        sub_sub_cancel_left, norm_neg, norm_div, hderiv x hx]
      exact div_le_div_of_nonneg_right (heval x hx) hd.le
    calc
      ‖f.newtonMap x - a₀‖ = ‖(f.newtonMap x - x) + (x - a₀)‖ := by congr 1; ring
      _ ≤ max ‖f.newtonMap x - x‖ ‖x - a₀‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le hstep hx
  have hcontract : ∀ x y : K, ‖x - a₀‖ ≤ r → ‖y - a₀‖ ≤ r →
      ‖f.newtonMap x - f.newtonMap y‖ ≤ (r / d) * ‖x - y‖ := by
    intro x y hx hy
    have hDx := hne x hx
    have hDy := hne y hy
    have ht : ‖x - y‖ ≤ r := by
      calc
        ‖x - y‖ = ‖(x - a₀) - (y - a₀)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ max ‖x - a₀‖ ‖y - a₀‖ := norm_sub_le_max _ _
        _ ≤ r := max_le hx hy
    -- Separate the Taylor remainder from the change of denominator.
    have hid : f.newtonMap x - f.newtonMap y =
        (f.eval y - f.eval x - f.derivative.eval x * (y - x)) / f.derivative.eval x +
        f.eval y * (f.derivative.eval x - f.derivative.eval y) /
          (f.derivative.eval x * f.derivative.eval y) := by
      simp only [newtonMap_apply_eq_sub_div, coe_aeval_eq_eval]
      field_simp [hDx, hDy]
      ring
    have hfirst : ‖(f.eval y - f.eval x - f.derivative.eval x * (y - x)) /
        f.derivative.eval x‖ ≤ (r / d) * ‖x - y‖ := by
      rw [norm_div, hderiv x hx]
      apply (div_le_iff₀ hd).2
      have hb := hTaylor y x (hunit y hy) (hunit x hx)
      rw [norm_sub_rev y x] at hb
      calc
        _ ≤ ‖x - y‖ ^ 2 := hb
        _ ≤ r * ‖x - y‖ := by
          simpa only [pow_two] using mul_le_mul_of_nonneg_right ht (norm_nonneg (x - y))
        _ = r / d * ‖x - y‖ * d := by field_simp
    have hsecond : ‖f.eval y * (f.derivative.eval x - f.derivative.eval y) /
        (f.derivative.eval x * f.derivative.eval y)‖ ≤ (r / d) * ‖x - y‖ := by
      rw [norm_div, norm_mul, norm_mul, hderiv x hx, hderiv y hy]
      apply (div_le_iff₀ (mul_pos hd hd)).2
      calc
        _ ≤ δ * ‖x - y‖ := mul_le_mul (heval y hy) (hLip x y (hunit x hx) (hunit y hy))
          (norm_nonneg _) hδ
        _ = r / d * ‖x - y‖ * (d * d) := by dsimp [r]; field_simp
    rw [hid]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hfirst hsecond)
  -- The subtype is only an adapter for Banach's theorem, not a new Newton sequence.
  let S := Metric.closedBall a₀ r
  let x₀ : S := ⟨a₀, by simpa [S] using hr⟩
  have hmem (x : S) : ‖(x : K) - a₀‖ ≤ r := by
    simpa only [S, Metric.mem_closedBall, dist_eq_norm] using x.property
  let F : S → S := fun x => ⟨f.newtonMap x, by
    simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hmap x (hmem x)⟩
  have : Nonempty S := ⟨x₀⟩
  have : IsClosed S := Metric.isClosed_closedBall
  let q : NNReal := ⟨r / d, div_nonneg hr hd.le⟩
  have hF : ContractingWith q F := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · exact (div_lt_one hd).2 hrd
    · rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
      change ‖f.newtonMap (x : K) - f.newtonMap (y : K)‖ ≤ r / d * ‖(x : K) - y‖
      exact hcontract x y (hmem x) (hmem y)
  let a := ContractingWith.fixedPoint F hF
  have ha : f.newtonMap (a : K) = a := congrArg Subtype.val hF.fixedPoint_isFixedPt
  have hroot : f.eval (a : K) = 0 := by
    have hfix : IsFixedPt f.newtonMap (a : K) := ha
    have hu : IsUnit (f.derivative.aeval (a : K)) := by
      rw [coe_aeval_eq_eval]
      exact isUnit_iff_ne_zero.mpr (hne a (hmem a))
    simpa only [coe_aeval_eq_eval] using (isFixedPt_newtonMap_of_isUnit_iff hu).mp hfix
  have hiter : ∀ n : ℕ, ((F^[n] x₀ : S) : K) = f.newtonMap^[n] a₀ := by
    intro n
    exact (show Semiconj (Subtype.val : S → K) F f.newtonMap from fun _ => rfl).iterate_right n x₀
  have hdist : ‖(a : K) - a₀‖ = r := by
    have hh := norm_eval_sub_eq_of_taylor (hTaylor a a₀ (hunit a (hmem a)) ha₀)
      ((hmem a).trans_lt hrd)
    rw [hroot, zero_sub, norm_neg] at hh
    exact (eq_div_iff hd.ne').2 (by simpa [mul_comm] using hh.symm)
  refine ⟨a, hroot, hunit a (hmem a), hdist, (hmem a).trans_lt hrd,
    hderiv a (hmem a), ?_, ?_, ?_⟩
  · have hh := (continuous_subtype_val.tendsto a).comp (hF.tendsto_iterate_fixedPoint x₀)
    simpa only [Function.comp_def, hiter] using hh
  · intro n
    have hn : ‖f.newtonMap^[n] a₀ - a₀‖ ≤ r := by
      rw [← hiter n]
      exact hmem (F^[n] x₀)
    exact ⟨hunit _ hn, hne _ hn, hderiv _ hn⟩
  · intro b hb hbd
    -- Every root in the larger open `d`-ball lies in the contraction ball.
    have hbunit : ‖b‖ ≤ 1 := by
      calc
        ‖b‖ = ‖(b - a₀) + a₀‖ := by rw [sub_add_cancel]
        _ ≤ max ‖b - a₀‖ ‖a₀‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le (hbd.le.trans hD) ha₀
    have hbS : ‖b - a₀‖ ≤ r := by
      have hh := norm_eval_sub_eq_of_taylor (hTaylor b a₀ hbunit ha₀) hbd
      rw [hb, zero_sub, norm_neg] at hh
      exact le_of_eq ((eq_div_iff hd.ne').2 (by simpa [mul_comm] using hh.symm))
    let bS : S := ⟨b, by simpa only [S, Metric.mem_closedBall, dist_eq_norm] using hbS⟩
    have hbfix : IsFixedPt F bS := by
      apply Subtype.ext
      exact isFixedPt_newtonMap_of_aeval_eq_zero (by simpa only [coe_aeval_eq_eval] using hb)
    exact congrArg Subtype.val (hF.fixedPoint_unique hbfix)

/-- Quantitative Newton lifting for an integral polynomial over a complete ultrametric
normed field. All Newton denominators are nonzero, the iterates stay integral and
converge to an integral root, and the derivative norm is preserved. The root is unique
in the open ball of radius `‖f.derivative.eval a₀‖` about `a₀`, and its distance from
`a₀` is exactly the initial error divided by the initial derivative norm.

This generalizes the monic complete-discrete-valuation-field statement in
Fesenko–Vostokov, *Local Fields and Their Extensions*, II, §1, Corollary 3 (p. 37),
and includes the explicit Newton convergence requested by Exercise 1 (p. 38).
The exact distance, derivative-norm stability, and uniqueness strengthen the source
conclusion and retain the full conclusion of Mathlib's p-adic `hensels_lemma`.
The coefficient norm bound replaces membership in a valuation integer ring. -/
theorem exists_root_tendsto_iterate_newtonMap
    {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {f : K[X]} {a₀ : K} (hf : ∀ n : ℕ, ‖f.coeff n‖ ≤ 1) (ha₀ : ‖a₀‖ ≤ 1)
    (hclose : ‖f.eval a₀‖ < ‖f.derivative.eval a₀‖ ^ 2) :
    ∃ a : K, f.eval a = 0 ∧ ‖a‖ ≤ 1 ∧
      ‖a - a₀‖ = ‖f.eval a₀‖ / ‖f.derivative.eval a₀‖ ∧
      ‖a - a₀‖ < ‖f.derivative.eval a₀‖ ∧
      ‖f.derivative.eval a‖ = ‖f.derivative.eval a₀‖ ∧
      Tendsto (fun n : ℕ => f.newtonMap^[n] a₀) atTop (𝓝 a) ∧
      (∀ n : ℕ, ‖f.newtonMap^[n] a₀‖ ≤ 1 ∧
        f.derivative.eval (f.newtonMap^[n] a₀) ≠ 0 ∧
        ‖f.derivative.eval (f.newtonMap^[n] a₀)‖ = ‖f.derivative.eval a₀‖) ∧
      ∀ b : K, f.eval b = 0 → ‖b - a₀‖ < ‖f.derivative.eval a₀‖ → b = a := by
  have hf' : ∀ n : ℕ, ‖f.derivative.coeff n‖ ≤ 1 :=
    norm_derivative_coeff_le_of_norm_coeff_le hf
  refine exists_root_of_newton_bounds ha₀
    (norm_eval_le_of_norm_coeff_le hf' ha₀) ?_ ?_ hclose
  · intro x y hx hy
    simpa only [one_mul] using norm_eval_sub_le_of_norm_coeff_le hf' hx hy
  · intro x y hx hy
    simpa only [one_mul] using norm_eval_sub_sub_derivative_mul_le_of_norm_coeff_le hf hx hy

end Polynomial
