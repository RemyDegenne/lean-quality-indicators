/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Padding a fixed polynomial substitution

An embedding of index types pads a family of substituted polynomials by zero.
The evaluation laws transfer a fixed outer polynomial's zero condition to the
substituted family. The homogeneity law does not require finite index types or
nonzero polynomials.
-/

set_option warningAsError true

namespace MvPolynomial

universe u v w z

variable {ι : Type u} {κ : Type v} {σ : Type w} {R : Type z} [CommSemiring R]

private theorem eval_aeval_pad (j : ι ↪ κ) (f : ι → MvPolynomial σ R)
    (p : MvPolynomial κ R) (x : σ → R) :
    eval x (aeval (Function.extend j f (fun _ => 0)) p) =
      eval (fun k => eval x (Function.extend j f (fun _ => 0) k)) p := by
  simpa only [aeval_eq_eval, aeval_eq_bind₁] using
    (aeval_bind₁ x (Function.extend j f (fun _ => 0)) p)

public section

/-- An outer polynomial vanishing only at the zero vector forces every
substituted polynomial to vanish whenever its zero-padded substitution does. -/
theorem eval_aeval_pad_eq_zero_imp (j : ι ↪ κ) (f : ι → MvPolynomial σ R)
    (p : MvPolynomial κ R) (h : ∀ y : κ → R, eval y p = 0 → y = 0)
    (x : σ → R) :
    eval x (aeval (Function.extend j f (fun _ => 0)) p) = 0 →
      ∀ i, eval x (f i) = 0 := by
  intro hx i
  have hz := h _ ((eval_aeval_pad j f p x).symm ▸ hx)
  have hi := congrFun hz (j i)
  simpa only [Pi.zero_apply, j.injective.extend_apply] using hi

/-- If an outer polynomial vanishes exactly at the zero vector, its zero-padded
substitution vanishes exactly when every substituted polynomial does. -/
theorem eval_aeval_pad_eq_zero_iff (j : ι ↪ κ) (f : ι → MvPolynomial σ R)
    (p : MvPolynomial κ R) (h : ∀ y : κ → R, eval y p = 0 ↔ y = 0)
    (x : σ → R) :
    eval x (aeval (Function.extend j f (fun _ => 0)) p) = 0 ↔
      ∀ i, eval x (f i) = 0 := by
  constructor
  · exact eval_aeval_pad_eq_zero_imp j f p (fun y => (h y).mp) x
  · intro hz
    rw [eval_aeval_pad]
    apply (h _).mpr
    funext k
    by_cases hk : ∃ i, j i = k
    · obtain ⟨i, rfl⟩ := hk
      simpa only [Pi.zero_apply, j.injective.extend_apply] using hz i
    · simp [Function.extend_apply' _ _ _ hk]

/-- Substitution of degree-`d` homogeneous polynomials into a degree-`e`
homogeneous polynomial, padding other indices by zero, is homogeneous of degree
`d * e`. The conclusion also applies when either degree is zero. -/
theorem IsHomogeneous.aeval_pad {p : MvPolynomial κ R} {e d : ℕ}
    (hp : p.IsHomogeneous e) (j : ι ↪ κ) (f : ι → MvPolynomial σ R)
    (hf : ∀ i, (f i).IsHomogeneous d) :
    (MvPolynomial.aeval (Function.extend j f (fun _ => 0)) p).IsHomogeneous (d * e) := by
  apply hp.aeval _
  intro k
  by_cases hk : ∃ i, j i = k
  · obtain ⟨i, rfl⟩ := hk
    simpa only [j.injective.extend_apply] using hf i
  · simpa only [Function.extend_apply' _ _ _ hk] using
      (isHomogeneous_zero (σ := σ) (R := R) d)

end

end MvPolynomial
