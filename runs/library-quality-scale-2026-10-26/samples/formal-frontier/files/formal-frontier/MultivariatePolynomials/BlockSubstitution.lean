/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad

set_option warningAsError true

/-!
# Substitution into disjoint blocks of variables

`blockSubst p q` replaces each variable `i` of `p` by a copy of `q` whose
variables are tagged by `i`. Evaluation therefore first evaluates `q` in each
block and then evaluates `p` at the resulting values.

## References

* Mathlib, `Mathlib.Algebra.MvPolynomial.Monad`: `bind₁`, `eval₂Hom_bind₁`
  and renaming; these supply the formalization approach to substitution.
-/

@[expose] public section

namespace MvPolynomial

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} [CommSemiring R]

/-- Substitute a separately tagged copy of `q` for each variable of `p`. -/
noncomputable def blockSubst (p : MvPolynomial ι R) (q : MvPolynomial κ R) :
    MvPolynomial (ι × κ) R :=
  bind₁ (fun i => rename (Prod.mk i) q) p

/-- Evaluation of disjoint-block substitution is evaluation in each block, then in `p`. -/
theorem eval_blockSubst (p : MvPolynomial ι R) (q : MvPolynomial κ R)
    (x : ι × κ → R) :
    eval x (blockSubst p q) = eval (fun i => eval (fun j => x (i, j)) q) p := by
  change eval₂Hom (RingHom.id R) x (bind₁ (fun i => rename (Prod.mk i) q) p) = _
  rw [eval₂Hom_bind₁]
  change eval (fun i => eval x (rename (Prod.mk i) q)) p = _
  simp_rw [eval_rename_prod_mk]

/-- If each factor can vanish only at the zero tuple, so can their block substitution. -/
theorem eval_blockSubst_eq_zero_imp (p : MvPolynomial ι R) (q : MvPolynomial κ R)
    (hp : ∀ y : ι → R, eval y p = 0 → y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 → z = 0)
    (x : ι × κ → R) : eval x (blockSubst p q) = 0 → x = 0 := by
  intro h
  rw [eval_blockSubst] at h
  have heval : (fun i => eval (fun j => x (i, j)) q) = 0 := hp _ h
  funext ⟨i, j⟩
  have hi : eval (fun k => x (i, k)) q = 0 := by
    simpa only [Pi.zero_apply] using congrFun heval i
  simpa only [Pi.zero_apply] using congrFun (hq _ hi) j

/-- Vanishing exactly at the zero tuple is preserved by disjoint-block substitution. -/
theorem eval_blockSubst_eq_zero_iff (p : MvPolynomial ι R) (q : MvPolynomial κ R)
    (hp : ∀ y : ι → R, eval y p = 0 ↔ y = 0)
    (hq : ∀ z : κ → R, eval z q = 0 ↔ z = 0)
    (x : ι × κ → R) : eval x (blockSubst p q) = 0 ↔ x = 0 := by
  refine ⟨eval_blockSubst_eq_zero_imp p q (fun y => (hp y).mp)
    (fun z => (hq z).mp) x, ?_⟩
  intro hx
  subst x
  rw [eval_blockSubst]
  have hq0 : eval (0 : κ → R) q = 0 := (hq 0).mpr rfl
  have hp0 : eval (0 : ι → R) p = 0 := (hp 0).mpr rfl
  have hinner : (fun i : ι => eval (fun j => (0 : ι × κ → R) (i, j)) q) = 0 := by
    funext i
    exact hq0
  rw [hinner]
  exact hp0

/-- Over a nontrivial semiring, a polynomial vanishing only at zero is nonzero
when it has at least one variable. No vanishing-at-zero assumption is needed. -/
theorem ne_zero_of_eval_eq_zero_imp [Nontrivial R] [Nonempty ι]
    (p : MvPolynomial ι R) (hp : ∀ y : ι → R, eval y p = 0 → y = 0) : p ≠ 0 := by
  intro hpzero
  have hones : (fun _ : ι => (1 : R)) = 0 := hp _ (by simp [hpzero])
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact one_ne_zero (congrFun hones i)

end MvPolynomial
