/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original formalization: Prism.
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Order comparison for ideal absolute norms

This file relates inclusion of ideals in a Dedekind domain to their absolute
norms. For a ring with finite quotients, strict inclusion reverses the strict
order on absolute norms as soon as the smaller ideal is nonzero. Consequently,
inclusion together with equality of absolute norms forces equality of ideals,
including when the smaller ideal is zero.
-/

public section

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
  [Ring.HasFiniteQuotients S] [Infinite S]

/-- Absolute norm is strictly antitone along strict inclusions whose smaller
ideal is nonzero. -/
theorem absNorm_lt_absNorm_of_lt {I J : Ideal S} (hIJ : I < J)
    (hI : I ≠ ⊥) : J.absNorm < I.absNorm := by
  let _ : I.toAddSubgroup.FiniteIndex := by
    rw [AddSubgroup.finiteIndex_iff, ← absNorm_eq_index]
    exact (absNorm_ne_zero_iff I).mpr
      (Ring.HasFiniteQuotients.finiteQuotient hI)
  have hltAdd : I.toAddSubgroup < J.toAddSubgroup := by
    refine lt_of_le_of_ne (fun _ hx ↦ hIJ.le hx) ?_
    intro heq
    exact hIJ.2 fun _ hx ↦ heq.ge hx
  simpa only [← absNorm_eq_index] using AddSubgroup.index_strictAnti hltAdd

/-- Nested ideals with equal absolute norm are equal. -/
theorem eq_of_le_of_absNorm_eq {I J : Ideal S} (hIJ : I ≤ J)
    (hnorm : I.absNorm = J.absNorm) : I = J := by
  apply le_antisymm hIJ
  by_contra hJI
  rcases eq_or_ne I ⊥ with rfl | hI
  · rw [absNorm_bot] at hnorm
    have hJ : J = ⊥ := by
      by_contra hJbot
      exact ((absNorm_ne_zero_iff J).mpr
        (Ring.HasFiniteQuotients.finiteQuotient hJbot)) hnorm.symm
    subst J
    exact hJI bot_le
  · have hlt : I < J := lt_of_le_of_ne hIJ fun hEq ↦ hJI (by rw [hEq])
    exact (absNorm_lt_absNorm_of_lt hlt hI).ne hnorm.symm

end Ideal
