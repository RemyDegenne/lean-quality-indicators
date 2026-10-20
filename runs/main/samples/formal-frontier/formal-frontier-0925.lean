set_option warningAsError true

namespace MvPolynomial

open Polynomial

variable {k : Type*} [Field k]

public section

theorem exists_nonzero_zero_ratFunc_of_single_form_bound (r : ℕ)
    (hsingle : ∀ (a t : ℕ) (p : MvPolynomial (Fin t) k),
      0 < a → a ^ r < t → p.IsHomogeneous a →
        ∃ x : Fin t → k, x ≠ 0 ∧ eval x p = 0)
    (d m : ℕ) (hd : 0 < d) (hsize : d ^ (r + 1) < m)
    (f : MvPolynomial (Fin m) (RatFunc k)) (hf : f.IsHomogeneous d) :
    ∃ x : Fin m → RatFunc k, x ≠ 0 ∧ eval x f = 0 := by
  classical
  obtain ⟨q, p, hq, hp, hcleared⟩ := clear_denominators m d f hf
  let degreeBound : ℕ := p.support.sup (fun exponent => (p.coeff exponent).natDegree)
  let parameterBound : ℕ := (degreeBound + 1) * d ^ r
  let equationBound : ℕ := degreeBound + d * parameterBound
  let flatten : Fin m × Fin (parameterBound + 1) ≃ Fin (m * (parameterBound + 1)) :=
    finProdFinEquiv
  have hcount : (equationBound + 1) * d ^ r < m * (parameterBound + 1) := by
    have hm : 0 < m := by omega
    have hminimum : d * d ^ r + 1 ≤ m := by
      simpa only [pow_succ, mul_comm] using Nat.add_one_le_iff.mpr hsize
    have heq : (equationBound + 1) * d ^ r =
        (d * d ^ r + 1) * parameterBound := by
      dsimp [equationBound, parameterBound]
      ring
    calc
      _ = (d * d ^ r + 1) * parameterBound := heq
      _ ≤ m * parameterBound := Nat.mul_le_mul_right _ hminimum
      _ < m * (parameterBound + 1) := Nat.mul_lt_mul_of_pos_left
        (Nat.lt_succ_self parameterBound) hm
  have hdegree : (interchange m parameterBound (substituted m parameterBound p)).natDegree ≤
      equationBound := by
    simpa only [equationBound, degreeBound, mul_comm] using
      interchange_degree_le m parameterBound d p hp
  let equations : Fin (equationBound + 1) →
      MvPolynomial (Fin (m * (parameterBound + 1))) k :=
    fun index => rename flatten
      ((interchange m parameterBound (substituted m parameterBound p)).coeff index.val)
  have hequations (index : Fin (equationBound + 1)) :
      (equations index).IsHomogeneous d :=
    (coefficient_homogeneous m parameterBound d index.val p hp).rename_isHomogeneous
  obtain ⟨flatPoint, hflatPoint, hflatZero⟩ :=
    exists_nonzero_common_zero_of_single_form_bound r hsingle d (equationBound + 1)
      (m * (parameterBound + 1)) hd hcount equations hequations
  let point : Fin m × Fin (parameterBound + 1) → k :=
    fun index => flatPoint (flatten index)
  have hpoint : point ≠ 0 := by
    intro hzero
    apply hflatPoint
    funext index
    have hi := congrFun hzero (flatten.symm index)
    simpa only [point, Equiv.apply_symm_apply, Pi.zero_apply] using hi
  have hcoeff (index : Fin (equationBound + 1)) :
      eval point
        ((interchange m parameterBound (substituted m parameterBound p)).coeff index.val) =
        0 := by
    have hi := hflatZero index
    simpa only [equations, eval_rename, Function.comp_def, point] using hi
  have hpolynomial : eval (polynomialPoint m parameterBound point) p = 0 :=
    zero_of_coefficients m parameterBound equationBound p hdegree point hcoeff
  let embedding : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  let rationalPoint : Fin m → RatFunc k :=
    fun index => embedding (polynomialPoint m parameterBound point index)
  have hrationalPoint : rationalPoint ≠ 0 := by
    intro hzero
    apply polynomialPoint_ne_zero m parameterBound point hpoint
    funext index
    apply RatFunc.algebraMap_injective k
    have hi := congrFun hzero index
    simpa only [rationalPoint, Pi.zero_apply, map_zero] using hi
  have hevaluation : eval rationalPoint (map embedding p) =
      embedding (eval (polynomialPoint m parameterBound point) p) := by
    rw [eval_map]
    change eval₂ embedding (embedding ∘ polynomialPoint m parameterBound point) p = _
    exact (eval₂_comp embedding (polynomialPoint m parameterBound point) p).symm
  have hzero : eval rationalPoint f = 0 := by
    have h := congrArg (eval rationalPoint) hcleared
    rw [hevaluation, hpolynomial, map_zero, eval_mul, eval_C] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (RatFunc.algebraMap_ne_zero hq)
  exact ⟨rationalPoint, hrationalPoint, hzero⟩

end
end MvPolynomial
