/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import NormForms.HomogeneousSystemZeros
public import MultivariatePolynomials.PolynomialCoefficientHomogeneity
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# A homogeneous-form zero bound over rational functions

The single-form bound over a field transfers to its field of rational functions.
The denominator clearing and finite polynomial-parameter calculations are internal.
-/

set_option warningAsError true

namespace MvPolynomial

open Polynomial

variable {k : Type*} [Field k]

private noncomputable def parameter (m s : ℕ) (index : Fin m) :
    MvPolynomial (Fin m × Fin (s + 1)) k[X] :=
  ∑ j : Fin (s + 1), C (Polynomial.X ^ j.val) * X (index, j)

private theorem parameter_homogeneous (m s : ℕ) (index : Fin m) :
    (parameter (k := k) m s index).IsHomogeneous 1 := by
  unfold parameter
  apply IsHomogeneous.sum Finset.univ _ _
  intro j _
  simpa only [zero_add] using
    (isHomogeneous_C (Fin m × Fin (s + 1))
      (Polynomial.X ^ j.val : k[X])).mul
      (isHomogeneous_X (R := k[X]) (index, j))

private noncomputable def substituted (m s : ℕ)
    (p : MvPolynomial (Fin m) k[X]) :
    MvPolynomial (Fin m × Fin (s + 1)) k[X] :=
  eval₂ C (parameter m s) p

private noncomputable def interchange (m s : ℕ)
    (p : MvPolynomial (Fin m × Fin (s + 1)) k[X]) :
    Polynomial (MvPolynomial (Fin m × Fin (s + 1)) k) :=
  ((optionEquivRight k (Fin m × Fin (s + 1))).symm.trans
    (optionEquivLeft k (Fin m × Fin (s + 1)))) p

private theorem interchange_C_C (m s : ℕ) (r : k) :
    interchange m s (C (Polynomial.C r)) =
      Polynomial.C (MvPolynomial.C r) := by
  change (optionEquivLeft k (Fin m × Fin (s + 1)))
    ((optionEquivRight k (Fin m × Fin (s + 1))).symm (C (Polynomial.C r))) = _
  rw [← optionEquivRight_C k (Fin m × Fin (s + 1)) r,
    AlgEquiv.symm_apply_apply, optionEquivLeft_C]

private theorem interchange_C_X (m s : ℕ) :
    interchange (k := k) m s (C Polynomial.X) = Polynomial.X := by
  change (optionEquivLeft k (Fin m × Fin (s + 1)))
    ((optionEquivRight k (Fin m × Fin (s + 1))).symm (C Polynomial.X)) = _
  rw [← optionEquivRight_X_none k (Fin m × Fin (s + 1)),
    AlgEquiv.symm_apply_apply, optionEquivLeft_X_none]

private theorem interchange_C (m s : ℕ) (b : k[X]) :
    interchange m s (C b) = Polynomial.map (C : k →+* MvPolynomial _ k) b := by
  let coefficientHom : k[X] →+* Polynomial (MvPolynomial (Fin m × Fin (s + 1)) k) :=
    (((optionEquivRight k (Fin m × Fin (s + 1))).symm.trans
      (optionEquivLeft k (Fin m × Fin (s + 1)))).toRingHom).comp C
  let mappedHom : k[X] →+* Polynomial (MvPolynomial (Fin m × Fin (s + 1)) k) :=
    Polynomial.mapRingHom C
  have hom_eq : coefficientHom = mappedHom := Polynomial.ringHom_ext
    (fun a => by
      change interchange m s (C (Polynomial.C a)) =
        Polynomial.map (C : k →+* MvPolynomial _ k) (Polynomial.C a)
      simpa only [Polynomial.map_C] using interchange_C_C m s a)
    (by
      change interchange (k := k) m s (C Polynomial.X) =
        Polynomial.map (C : k →+* MvPolynomial _ k) Polynomial.X
      simpa only [Polynomial.map_X] using interchange_C_X (k := k) m s)
  exact congrArg (fun hom : k[X] →+* Polynomial (MvPolynomial _ k) => hom b) hom_eq

private theorem interchange_X (m s : ℕ) (i : Fin m × Fin (s + 1)) :
    interchange (k := k) m s (X i) = Polynomial.C (MvPolynomial.X i) := by
  change (optionEquivLeft k (Fin m × Fin (s + 1)))
    ((optionEquivRight k (Fin m × Fin (s + 1))).symm (X i)) = _
  rw [← optionEquivRight_X_some k (Fin m × Fin (s + 1)) i,
    AlgEquiv.symm_apply_apply, optionEquivLeft_X_some]

private noncomputable def parameterPolynomial (m s : ℕ) (i : Fin m) :
    Polynomial (MvPolynomial (Fin m × Fin (s + 1)) k) :=
  ∑ j : Fin (s + 1), Polynomial.C (MvPolynomial.X (i, j)) * Polynomial.X ^ j.val

private theorem interchange_parameter (m s : ℕ) (i : Fin m) :
    interchange m s (parameter (k := k) m s i) = parameterPolynomial m s i := by
  unfold parameterPolynomial
  calc
    interchange m s (parameter m s i) =
        ∑ j : Fin (s + 1),
          interchange m s (C (Polynomial.X ^ j.val)) * interchange m s (X (i, j)) := by
      unfold parameter interchange
      simp only [map_sum, map_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [interchange_C, interchange_X, Polynomial.map_pow, Polynomial.map_X, mul_comm]

private theorem coefficient_homogeneous (m s d n : ℕ)
    (p : MvPolynomial (Fin m) k[X]) (hp : p.IsHomogeneous d) :
    ((interchange m s (substituted m s p)).coeff n).IsHomogeneous d := by
  apply IsHomogeneous.coeff_polynomial_interchange _ d n
  change (eval₂ C (parameter m s) p).IsHomogeneous d
  simpa only [one_mul] using
    hp.eval₂ (C : k[X] →+* MvPolynomial (Fin m × Fin (s + 1)) k[X])
      (parameter m s)
      (fun b => isHomogeneous_C _ b)
      (parameter_homogeneous m s)

private theorem interchange_substituted (m s : ℕ)
    (p : MvPolynomial (Fin m) k[X]) :
    interchange m s (substituted m s p) =
      eval₂ (Polynomial.mapRingHom (C : k →+* MvPolynomial _ k))
        (parameterPolynomial m s) p := by
  let J : MvPolynomial (Fin m × Fin (s + 1)) k[X] →+*
      Polynomial (MvPolynomial (Fin m × Fin (s + 1)) k) :=
    (((optionEquivRight k (Fin m × Fin (s + 1))).symm.trans
      (optionEquivLeft k (Fin m × Fin (s + 1)))).toRingHom)
  change J (eval₂ C (parameter m s) p) = _
  rw [eval₂_comp_left J C (parameter m s) p]
  have hC : J.comp (C : k[X] →+* MvPolynomial _ k[X]) =
      Polynomial.mapRingHom (C : k →+* MvPolynomial _ k) := by
    apply DFunLike.ext
    intro b
    exact interchange_C m s b
  rw [hC]
  congr 1
  funext i
  exact interchange_parameter m s i

private noncomputable def polynomialPoint (m s : ℕ)
    (a : Fin m × Fin (s + 1) → k) (i : Fin m) : k[X] :=
  ∑ j : Fin (s + 1), Polynomial.C (a (i, j)) * Polynomial.X ^ j.val

private theorem interchange_naturality (m s : ℕ)
    (p : MvPolynomial (Fin m) k[X]) (a : Fin m × Fin (s + 1) → k) :
    Polynomial.map (eval a) (interchange m s (substituted m s p)) =
      eval (polynomialPoint m s a) p := by
  have hcomp : (Polynomial.mapRingHom (eval a)).comp
      (Polynomial.mapRingHom (C : k →+* MvPolynomial _ k)) = RingHom.id k[X] := by
    apply Polynomial.ringHom_ext
    · intro b
      simp
    · simp
  have hpoint (i : Fin m) :
      Polynomial.map (eval a) (parameterPolynomial m s i) =
        polynomialPoint m s a i := by
    unfold parameterPolynomial polynomialPoint
    change (Polynomial.mapRingHom (eval a))
      (∑ j : Fin (s + 1), Polynomial.C (X (i, j)) * Polynomial.X ^ j.val) = _
    simp only [map_sum, map_mul, map_pow]
    change (∑ j : Fin (s + 1),
      Polynomial.map (eval a) (Polynomial.C (X (i, j))) *
        (Polynomial.map (eval a) Polynomial.X) ^ j.val) = _
    simp only [Polynomial.map_C, Polynomial.map_X, eval_X]
  rw [interchange_substituted]
  change (Polynomial.mapRingHom (eval a))
    (eval₂ (Polynomial.mapRingHom C) (parameterPolynomial m s) p) = _
  rw [eval₂_comp_left, hcomp]
  change eval (fun i => Polynomial.map (eval a) (parameterPolynomial m s i)) p = _
  rw [show (fun i => Polynomial.map (eval a) (parameterPolynomial m s i)) =
    polynomialPoint m s a from funext hpoint]

private theorem parameterPolynomial_degree_le (m s : ℕ) (i : Fin m) :
    (parameterPolynomial (k := k) m s i).natDegree ≤ s := by
  unfold parameterPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ j.isLt)

private theorem interchange_degree_le (m s d : ℕ)
    (p : MvPolynomial (Fin m) k[X]) (hp : p.IsHomogeneous d) :
    (interchange m s (substituted m s p)).natDegree ≤
      p.support.sup (fun exponent => (p.coeff exponent).natDegree) + s * d := by
  classical
  rw [interchange_substituted]
  conv_lhs => rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  have hcoefficient : (p.coeff exponent).natDegree ≤
      p.support.sup (fun index => (p.coeff index).natDegree) :=
    Finset.le_sup (f := fun index => (p.coeff index).natDegree) hexponent
  have hdegree : exponent.degree = d := by
    change (∑ i ∈ exponent.support, exponent i) = d
    simpa [Finsupp.weight_apply, Finsupp.sum]
      using hp (Finsupp.mem_support_iff.mp hexponent)
  have hproduct :
      (exponent.prod fun i e => (parameterPolynomial (k := k) m s i) ^ e).natDegree ≤
        s * exponent.degree := by
    calc
      _ ≤ ∑ i ∈ exponent.support,
          ((parameterPolynomial (k := k) m s i) ^ exponent i).natDegree := by
        simpa only [Finsupp.prod] using
          (Polynomial.natDegree_prod_le (s := exponent.support)
            (f := fun i : Fin m => (parameterPolynomial (k := k) m s i) ^ exponent i))
      _ ≤ ∑ i ∈ exponent.support, s * exponent i := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ exponent i * (parameterPolynomial (k := k) m s i).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ exponent i * s := Nat.mul_le_mul_left _ (parameterPolynomial_degree_le m s i)
          _ = s * exponent i := mul_comm _ _
      _ = _ := by
        change (∑ i ∈ exponent.support, s * exponent i) =
          s * (∑ i ∈ exponent.support, exponent i)
        rw [Finset.mul_sum]
  calc
    _ ≤ (Polynomial.map (C : k →+* MvPolynomial _ k) (p.coeff exponent)).natDegree +
        (exponent.prod fun i e => (parameterPolynomial m s i) ^ e).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (p.coeff exponent).natDegree + s * exponent.degree := by
      exact add_le_add Polynomial.natDegree_map_le hproduct
    _ ≤ _ := by rw [hdegree]; omega

private theorem polynomialPoint_coeff (m s : ℕ)
    (a : Fin m × Fin (s + 1) → k) (i : Fin m) (j : Fin (s + 1)) :
    (polynomialPoint m s a i).coeff j.val = a (i, j) := by
  classical
  simp only [polynomialPoint, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro index _ hne
    simp [Fin.val_inj, hne.symm]
  · simp

private theorem polynomialPoint_ne_zero (m s : ℕ)
    (a : Fin m × Fin (s + 1) → k) (ha : a ≠ 0) :
    polynomialPoint m s a ≠ 0 := by
  intro hzero
  apply ha
  funext ⟨i, j⟩
  have hi := congrFun hzero i
  have hj := congrArg (fun b : k[X] => b.coeff j.val) hi
  simpa only [polynomialPoint_coeff, Pi.zero_apply, Polynomial.coeff_zero]
    using hj

private theorem zero_of_coefficients (m s bound : ℕ)
    (p : MvPolynomial (Fin m) k[X])
    (hbound : (interchange m s (substituted m s p)).natDegree ≤ bound)
    (a : Fin m × Fin (s + 1) → k)
    (hcoeff : ∀ index : Fin (bound + 1),
      eval a ((interchange m s (substituted m s p)).coeff index.val) = 0) :
    eval (polynomialPoint m s a) p = 0 := by
  apply Polynomial.ext
  intro n
  have heval : (eval (polynomialPoint m s a) p).coeff n =
      eval a ((interchange m s (substituted m s p)).coeff n) := by
    rw [← Polynomial.coeff_map, interchange_naturality]
  rw [heval, Polynomial.coeff_zero]
  by_cases hn : n < bound + 1
  · exact hcoeff ⟨n, hn⟩
  · have hbig : bound < n := by omega
    rw [(Polynomial.natDegree_le_iff_coeff_eq_zero.mp hbound) n hbig, map_zero]

private theorem clear_denominators (m d : ℕ)
    (f : MvPolynomial (Fin m) (RatFunc k)) (hf : f.IsHomogeneous d) :
    ∃ (q : k[X]) (p : MvPolynomial (Fin m) k[X]), q ≠ 0 ∧
      p.IsHomogeneous d ∧
        map (algebraMap k[X] (RatFunc k)) p =
          C (algebraMap k[X] (RatFunc k) q) * f := by
  classical
  let embedding : k[X] →+* RatFunc k := algebraMap k[X] (RatFunc k)
  let q : k[X] := ∏ exponent ∈ f.support, (f.coeff exponent).denom
  let p : MvPolynomial (Fin m) k[X] :=
    ∑ exponent ∈ f.support,
      monomial exponent ((f.coeff exponent).num *
        ∏ other ∈ f.support.erase exponent, (f.coeff other).denom)
  have hq : q ≠ 0 := by
    unfold q
    exact Finset.prod_ne_zero_iff.mpr
      (fun exponent _ => RatFunc.denom_ne_zero (f.coeff exponent))
  have hsupport : p.support ⊆ f.support := by
    intro exponent hexponent
    by_contra hnot
    have hcoeff : p.coeff exponent = 0 := by
      simp only [p, coeff_sum, coeff_monomial]
      apply Finset.sum_eq_zero
      intro index hindex
      have hne : index ≠ exponent := fun heq => hnot (heq ▸ hindex)
      simp [hne]
    exact (Finsupp.mem_support_iff.mp hexponent) hcoeff
  have hp : p.IsHomogeneous d := by
    intro exponent hexponent
    exact hf (Finsupp.mem_support_iff.mp
      (hsupport (Finsupp.mem_support_iff.mpr hexponent)))
  have hfraction (exponent : Fin m →₀ ℕ) (hexponent : exponent ∈ f.support) :
      embedding ((f.coeff exponent).num *
        ∏ other ∈ f.support.erase exponent, (f.coeff other).denom) =
      embedding q * f.coeff exponent := by
    let denominator : k[X] := (f.coeff exponent).denom
    let complement : k[X] :=
      ∏ other ∈ f.support.erase exponent, (f.coeff other).denom
    have hden : embedding denominator ≠ 0 :=
      RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (f.coeff exponent))
    have hprod : denominator * complement = q := by
      exact Finset.mul_prod_erase f.support
        (fun index => (f.coeff index).denom) hexponent
    change embedding ((f.coeff exponent).num * complement) = _
    calc
      embedding ((f.coeff exponent).num * complement) =
          embedding (f.coeff exponent).num * embedding complement := map_mul _ _ _
      _ = (embedding (f.coeff exponent).num / embedding denominator) *
          (embedding denominator * embedding complement) := by field_simp
      _ = embedding q * f.coeff exponent := by
        rw [RatFunc.num_div_denom, ← map_mul, hprod, mul_comm]
  refine ⟨q, p, hq, hp, ?_⟩
  change map embedding
      (∑ exponent ∈ f.support,
        monomial exponent ((f.coeff exponent).num *
          ∏ other ∈ f.support.erase exponent, (f.coeff other).denom)) =
    C (embedding q) * f
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, map_monomial, Finset.mul_sum, C_mul_monomial]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  congr 1
  exact hfraction exponent hexponent

public section

/-- A uniform positive-degree single-form zero bound passes from a field to its
rational-function field, at the degree bound multiplied by one extra factor of
the degree. Zero forms and the case `r = 0` are included. -/
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
