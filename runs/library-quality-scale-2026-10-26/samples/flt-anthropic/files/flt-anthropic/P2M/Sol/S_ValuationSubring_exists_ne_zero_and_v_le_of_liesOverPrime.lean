import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
namespace P2MW.S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ε : A.ValueGroup) (hε : ε ≠ 0) :
    ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y ≤ ε := by
  obtain ⟨x, hx⟩ := A.valuation_surjective ε
  refine ⟨((WithVal.toVal A.valuation x : WithVal A.valuation) : A.valuation.Completion), ?_, ?_⟩
  · intro h
    apply hε
    have := congrArg (Valued.v (R := A.valuation.Completion)) h
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx, map_zero] at this
    exact this
  · rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx]
