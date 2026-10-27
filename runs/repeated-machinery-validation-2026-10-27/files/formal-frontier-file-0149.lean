/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.AlgebraicallyClosedCommonZero
public import NormForms.CoordinateNormIteration
public import NormForms.PaddedSubstitution
public import SequenceGrowth.Data.Nat.DivisionGrowth

/-!
# Common zeros of equally labelled homogeneous polynomials

A single-form nontrivial-zero bound, assumed uniformly in every positive degree,
implies the sharp equal-degree simultaneous bound over an arbitrary field.
Neither the forms nor the equations are required to be nonzero or distinct.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

namespace MvPolynomial

open Nat

private theorem homogeneous_block_step {K : Type*} [Field K]
    (s n N d D : ℕ) (f : Fin s → MvPolynomial (Fin n) K)
    (p : MvPolynomial (Fin N) K)
    (hf : ∀ i, (f i).IsHomogeneous d)
    (hfzero : ∀ x : Fin n → K, (∀ i, eval x (f i) = 0) → x = 0)
    (hp : p.IsHomogeneous D)
    (hpzero : ∀ x : Fin N → K, eval x p = 0 → x = 0) :
    ∃ q : MvPolynomial (Fin (n * (N / s))) K,
      q.IsHomogeneous (d * D) ∧
        ∀ x : Fin (n * (N / s)) → K, eval x q = 0 → x = 0 := by
  classical
  let blocks := N / s
  let slots : Fin blocks × Fin s ≃ Fin (s * blocks) :=
    Fintype.equivOfCardEq (by simp [mul_comm])
  let inclusion : Fin blocks × Fin s ↪ Fin N :=
    { toFun := fun index =>
        ⟨(slots index).val, lt_of_lt_of_le (slots index).isLt
          (by dsimp [blocks]; exact Nat.mul_div_le N s)⟩
      inj' := by
        intro first second heq
        apply slots.injective
        apply Fin.ext
        simpa only using congrArg Fin.val heq }
  let flatten : Fin blocks × Fin n ≃ Fin (n * blocks) :=
    Fintype.equivOfCardEq (by simp [mul_comm])
  let inner : Fin blocks × Fin s → MvPolynomial (Fin blocks × Fin n) K :=
    fun index => rename (fun coordinate => (index.1, coordinate)) (f index.2)
  let substituted := aeval (Function.extend inclusion inner (fun _ => 0)) p
  refine ⟨rename flatten substituted, ?_, ?_⟩
  · exact (hp.aeval_pad inclusion inner
      (fun index => (hf index.2).rename_isHomogeneous)).rename_isHomogeneous
  · intro x hx
    have hsub : eval (x ∘ flatten) substituted = 0 := by
      simpa only [eval_rename] using hx
    have hinner := eval_aeval_pad_eq_zero_imp inclusion inner p hpzero
      (x ∘ flatten) hsub
    have hblock (index : Fin blocks) :
        (fun coordinate : Fin n => x (flatten (index, coordinate))) = 0 := by
      apply hfzero
      intro equation
      have heq := hinner (index, equation)
      simpa only [inner, eval_rename, Function.comp_def] using heq
    funext coordinate
    obtain ⟨index, rfl⟩ := flatten.surjective coordinate
    exact congrFun (hblock index.1) index.2

public section

/-- If every positive-degree homogeneous form in more than its degree to the
`r`-th power variables has a nontrivial zero, then `s` homogeneous forms of
the same positive degree `d` have a nontrivial common zero whenever
`s * d ^ r < n`. The equations may be zero or repeated, and `s = 0` is allowed. -/
theorem exists_nonzero_common_zero_of_single_form_bound {K : Type*} [Field K]
    (r : ℕ)
    (hsingle : ∀ (a t : ℕ) (p : MvPolynomial (Fin t) K),
      0 < a → a ^ r < t → p.IsHomogeneous a →
        ∃ x : Fin t → K, x ≠ 0 ∧ eval x p = 0)
    (d s n : ℕ) (hd : 0 < d) (hsize : s * d ^ r < n)
    (f : Fin s → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).IsHomogeneous d) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  classical
  have hn : 0 < n := by omega
  by_cases hs : s = 0
  · let first : Fin n := ⟨0, hn⟩
    let x : Fin n → K := fun i => if i = first then 1 else 0
    refine ⟨x, ?_, ?_⟩
    · intro hx
      have hfirst := congrFun hx first
      simp [x] at hfirst
    · intro i
      exact (hs ▸ i).elim0
  have hspos : 0 < s := by omega
  have hds : 0 < d ^ r := pow_pos hd r
  have hsn : s < n := by nlinarith
  by_cases hclosed : IsAlgClosed K
  · letI : IsAlgClosed K := hclosed
    apply exists_nonzero_common_zero_of_isHomogeneous f (fun _ => d)
    · simpa using hsn
    · exact fun _ => hd
    · exact hf
  by_contra hnoexist
  have hfzero : ∀ x : Fin n → K, (∀ i, eval x (f i) = 0) → x = 0 := by
    intro x hx
    by_contra hxzero
    exact hnoexist ⟨x, hxzero, hx⟩
  obtain ⟨e, seed, he, hseedHom, _, hseedZero⟩ :=
    exists_anisotropic_homogeneous_of_not_isAlgClosed K hclosed
      (max s (n * (s - 1)))
  have hepos : 0 < e := by omega
  have hseed : n * (s - 1) < (n - s) * e := by
    have hlt : n * (s - 1) < e := lt_of_le_of_lt (le_max_right _ _) he
    have hdiff : 1 ≤ n - s := by omega
    nlinarith [Nat.mul_le_mul_right e hdiff]
  let arity : ℕ → ℕ := Nat.rec e (fun _ previous => n * (previous / s))
  have hiterate (m : ℕ) :
      ∃ p : MvPolynomial (Fin (arity m)) K,
        p.IsHomogeneous (d ^ m * e) ∧
          ∀ x : Fin (arity m) → K, eval x p = 0 → x = 0 := by
    induction m with
    | zero =>
        exact ⟨seed, by simpa [arity] using hseedHom,
          by simpa [arity] using (fun x hx => (hseedZero x).mp hx)⟩
    | succ m ih =>
        obtain ⟨p, hp, hpzero⟩ := ih
        obtain ⟨q, hq, hqzero⟩ :=
          homogeneous_block_step s n (arity m) d (d ^ m * e) f p hf hfzero hp hpzero
        refine ⟨q, ?_, hqzero⟩
        convert hq using 1
        simp [pow_succ, mul_left_comm, mul_comm]
  obtain ⟨M, hM⟩ := Nat.DivisionGrowth.eventually_dominates arity s n
    (d ^ r) hspos hds hsize (by simpa [arity] using hseed)
    (fun m => by rfl) (e ^ r)
  obtain ⟨p, hp, hpzero⟩ := hiterate M
  have hbound : (d ^ M * e) ^ r < arity M := by
    calc
      (d ^ M * e) ^ r = e ^ r * (d ^ r) ^ M := by
        calc
          (d ^ M * e) ^ r = d ^ (M * r) * e ^ r := by rw [mul_pow, pow_mul]
          _ = e ^ r * d ^ (r * M) := by rw [mul_comm M r, mul_comm]
          _ = e ^ r * (d ^ r) ^ M := by rw [pow_mul]
      _ < arity M := hM M le_rfl
  obtain ⟨x, hx, hzero⟩ := hsingle (d ^ M * e) (arity M) p
    (mul_pos (pow_pos hd M) hepos) hbound hp
  exact hx (hpzero x hzero)

end

end MvPolynomial
