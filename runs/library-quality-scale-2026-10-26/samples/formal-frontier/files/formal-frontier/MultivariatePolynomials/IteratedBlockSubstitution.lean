/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.BlockSubstitution
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

set_option warningAsError true

/-!
# Iterated substitution into disjoint variable blocks

`iteratedBlockSubst p r` uses variables indexed by length-`r` tuples of
indices of `p`. Zero iterations yield the empty-tuple variable; a successor
substitutes the preceding iterate into disjoint blocks and renames by
`Fin.consEquiv`. Import this module directly or use `MultivariatePolynomials`.

## References

* `MultivariatePolynomials.BlockSubstitution`: the disjoint-block operation
  iterated here.
* Mathlib, `Mathlib.Data.Fin.Tuple.Basic` (`Fin.consEquiv`) and
  `Mathlib.RingTheory.MvPolynomial.Homogeneous` (homogeneous-degree laws).

-/

@[expose] public section

namespace MvPolynomial

universe u v

variable {ι : Type u} {R : Type v} [CommSemiring R]

/-- Iterate disjoint-block substitution, with the empty-tuple variable as identity. -/
noncomputable def iteratedBlockSubst (p : MvPolynomial ι R) :
    (r : ℕ) → MvPolynomial (Fin r → ι) R
  | 0 => X Fin.elim0
  | r + 1 => rename (Fin.consEquiv (fun _ : Fin (r + 1) => ι))
      (blockSubst p (iteratedBlockSubst p r))

@[simp]
theorem iteratedBlockSubst_zero (p : MvPolynomial ι R) :
    iteratedBlockSubst p 0 = X Fin.elim0 := rfl

theorem iteratedBlockSubst_succ (p : MvPolynomial ι R) (r : ℕ) :
    iteratedBlockSubst p (r + 1) =
      rename (Fin.consEquiv (fun _ : Fin (r + 1) => ι))
        (blockSubst p (iteratedBlockSubst p r)) := rfl

@[simp]
theorem eval_iteratedBlockSubst_zero (p : MvPolynomial ι R)
    (x : (Fin 0 → ι) → R) : eval x (iteratedBlockSubst p 0) = x Fin.elim0 := by
  simp [iteratedBlockSubst]

theorem eval_iteratedBlockSubst_succ (p : MvPolynomial ι R) (r : ℕ)
    (x : (Fin (r + 1) → ι) → R) :
    eval x (iteratedBlockSubst p (r + 1)) =
      eval (fun i => eval (fun t => x (Fin.cons i t)) (iteratedBlockSubst p r)) p := by
  rw [iteratedBlockSubst_succ, eval_rename, eval_blockSubst]
  rfl

/-- If `p` can vanish only at the zero tuple, so can every finite iteration. -/
theorem eval_iteratedBlockSubst_eq_zero_imp (p : MvPolynomial ι R)
    (hp : ∀ x : ι → R, eval x p = 0 → x = 0) (r : ℕ)
    (x : (Fin r → ι) → R) : eval x (iteratedBlockSubst p r) = 0 → x = 0 := by
  induction r with
  | zero =>
      intro hx
      funext j
      have hj : j = (Fin.elim0 : Fin 0 → ι) := Subsingleton.elim _ _
      simpa only [hj, Pi.zero_apply, eval_iteratedBlockSubst_zero] using hx
  | succ r ih =>
      intro hx
      let e := Fin.consEquiv (fun _ : Fin (r + 1) => ι)
      have he : (fun t => x (e t)) = 0 :=
        eval_blockSubst_eq_zero_imp p (iteratedBlockSubst p r) hp ih _
          (by simpa only [iteratedBlockSubst_succ, eval_rename, Function.comp_def] using hx)
      funext j
      have hj := congrFun he (e.symm j)
      simpa only [Pi.zero_apply, Equiv.apply_symm_apply] using hj

/-- The stronger property of vanishing exactly at zero also survives iteration. -/
theorem eval_iteratedBlockSubst_eq_zero_iff (p : MvPolynomial ι R)
    (hp : ∀ x : ι → R, eval x p = 0 ↔ x = 0) (r : ℕ)
    (x : (Fin r → ι) → R) : eval x (iteratedBlockSubst p r) = 0 ↔ x = 0 := by
  induction r with
  | zero =>
      constructor
      · exact eval_iteratedBlockSubst_eq_zero_imp p (fun y => (hp y).mp) _ _
      · intro hx
        subst x
        simp only [eval_iteratedBlockSubst_zero, Pi.zero_apply]
  | succ r ih =>
      constructor
      · exact eval_iteratedBlockSubst_eq_zero_imp p (fun y => (hp y).mp) _ _
      · intro hx
        have hzero : (fun t : ι × (Fin r → ι) => (0 : (Fin (r + 1) → ι) → R)
            ((Fin.consEquiv (fun _ : Fin (r + 1) => ι)) t)) = 0 := by
          funext t
          rfl
        have h := (eval_blockSubst_eq_zero_iff p (iteratedBlockSubst p r) hp ih _).mpr hzero
        subst x
        simpa only [iteratedBlockSubst_succ, eval_rename, Function.comp_def] using h

/-- Homogeneous degree multiplies by the base degree at every successor. -/
theorem isHomogeneous_iteratedBlockSubst (p : MvPolynomial ι R) (d : ℕ)
    (hp : p.IsHomogeneous d) (r : ℕ) :
    (iteratedBlockSubst p r).IsHomogeneous (d ^ r) := by
  induction r with
  | zero =>
      simpa only [iteratedBlockSubst_zero, pow_zero] using
        (isHomogeneous_X R (Fin.elim0 : Fin 0 → ι))
  | succ r ih =>
      have hblock : (blockSubst p (iteratedBlockSubst p r)).IsHomogeneous
          (d ^ r * d) := by
        change (aeval (fun i => rename (Prod.mk i) (iteratedBlockSubst p r)) p).IsHomogeneous
          (d ^ r * d)
        exact hp.aeval _ (fun i => ih.rename_isHomogeneous)
      simpa only [iteratedBlockSubst_succ, pow_succ] using
        (hblock.rename_isHomogeneous
          (f := (Fin.consEquiv (fun _ : Fin (r + 1) => ι) :
            (ι × (Fin r → ι)) ≃ (Fin (r + 1) → ι))))

/-- Nontrivial coefficients and a variable make the forward-only property nonvacuous. -/
theorem iteratedBlockSubst_ne_zero [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (hp : ∀ x : ι → R, eval x p = 0 → x = 0) (r : ℕ) :
    iteratedBlockSubst p r ≠ 0 := by
  exact ne_zero_of_eval_eq_zero_imp _ (eval_iteratedBlockSubst_eq_zero_imp p hp r)

/-- The nominal homogeneous degree equals total degree when the iteration is nonzero. -/
theorem iteratedBlockSubst_totalDegree [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ x : ι → R, eval x p = 0 → x = 0) (r : ℕ) :
    (iteratedBlockSubst p r).totalDegree = d ^ r :=
  (isHomogeneous_iteratedBlockSubst p d hp r).totalDegree
    (iteratedBlockSubst_ne_zero p hz r)

/-- Degrees attained by the iterates exceed any prescribed bound when `1 < d`. -/
theorem exists_iteratedBlockSubst_totalDegree_gt [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (d : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ x : ι → R, eval x p = 0 → x = 0) (hd : 1 < d) (bound : ℕ) :
    ∃ r : ℕ, bound < (iteratedBlockSubst p r).totalDegree := by
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt bound hd
  exact ⟨r, by simpa only [iteratedBlockSubst_totalDegree p d hp hz r] using hr⟩

end MvPolynomial
