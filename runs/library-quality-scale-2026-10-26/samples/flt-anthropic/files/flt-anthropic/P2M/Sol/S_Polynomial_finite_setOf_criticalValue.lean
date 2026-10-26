import Mathlib
import P2M.Util
namespace P2MW.S_Polynomial_finite_setOf_criticalValue

set_option autoImplicit false

open Polynomial

universe u

theorem solution
    {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by
  have hfin : {x : k | (derivative P).eval x = 0}.Finite := (derivative P).finite_setOf_isRoot hP
  refine (hfin.image fun x => P.eval x).subset ?_
  rintro c ⟨x, rfl, hx⟩
  exact ⟨x, hx, rfl⟩
