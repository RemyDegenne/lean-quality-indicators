/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Tactic.Abel

/-!
# Bass stable-range conditions

This file defines finite right-unimodular rows and Bass's stable-range
conditions for arbitrary, possibly noncommutative rings. The multiplication
order is explicit: witnesses occur on the right of the row entries.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter I, §1.2 and Exercise I.1.5 (unimodular rows and Bass stable range).
* Mathlib, for finite sums and ring equivalences used to express these conditions.
-/

set_option warningAsError true

@[expose] public section

open Function
open scoped BigOperators

namespace Bass

universe u v

/-- A finite row is right-unimodular when its entries generate `1` by a right
linear combination. -/
def IsRightUnimodular {R : Type u} [Ring R] {n : ℕ} (r : Fin n → R) : Prop :=
  ∃ s : Fin n → R, ∑ i, r i * s i = 1

/-- Right-unimodularity with a distinguished first entry separated from the
remaining finite row. -/
def IsRightUnimodularCons {R : Type u} [Ring R] {n : ℕ}
    (r0 : R) (r : Fin n → R) : Prop :=
  ∃ (s0 : R) (s : Fin n → R), r0 * s0 + ∑ i, r i * s i = 1

/-- Separating the first coordinate preserves right-unimodularity. -/
theorem isRightUnimodular_finSucc_iff {R : Type u} [Ring R] {n : ℕ}
    (r : Fin (n + 1) → R) :
    IsRightUnimodular r ↔
      IsRightUnimodularCons (r 0) (fun i ↦ r i.succ) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s 0, fun i ↦ s i.succ, ?_⟩
    simpa [IsRightUnimodular, IsRightUnimodularCons, Fin.sum_univ_succ] using hs
  · rintro ⟨s0, s, hs⟩
    refine ⟨Fin.cases s0 s, ?_⟩
    simpa [IsRightUnimodular, IsRightUnimodularCons, Fin.sum_univ_succ] using hs

/-- Bass's condition `(S_n)`, stated with the distinguished first coordinate
separated from a row of length `n`; see Weibel, *The K-book*, Exercise I.1.5. -/
def StableRangeCondition (R : Type u) [Ring R] (n : ℕ) : Prop :=
  ∀ (r0 : R) (r : Fin n → R), IsRightUnimodularCons r0 r →
    ∃ t : Fin n → R, IsRightUnimodular (fun i ↦ r i - r0 * t i)

/-- The separated form of `(S_n)` is equivalent to its literal formulation on
a right-unimodular row of length `n + 1`. -/
theorem stableRangeCondition_iff_literal {R : Type u} [Ring R] (n : ℕ) :
    StableRangeCondition R n ↔
      ∀ (r : Fin (n + 1) → R), IsRightUnimodular r →
        ∃ t : Fin n → R,
          IsRightUnimodular (fun i ↦ r i.succ - r 0 * t i) := by
  constructor
  · intro h r hr
    exact h (r 0) (fun i ↦ r i.succ)
      ((isRightUnimodular_finSucc_iff r).mp hr)
  · intro h r0 r hr
    let row : Fin (n + 1) → R := Fin.cases r0 r
    have hrow : IsRightUnimodular row := by
      apply (isRightUnimodular_finSucc_iff row).mpr
      simpa [row] using hr
    simpa [row] using h row hrow

/-- A ring homomorphism preserves right-unimodularity. -/
theorem IsRightUnimodular.map {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) {n : ℕ} {r : Fin n → R} (hr : IsRightUnimodular r) :
    IsRightUnimodular (fun i ↦ f (r i)) := by
  obtain ⟨w, hw⟩ := hr
  refine ⟨fun i ↦ f (w i), ?_⟩
  simpa using congrArg f hw

/-- A ring homomorphism preserves the separated form of
right-unimodularity. -/
theorem IsRightUnimodularCons.map
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) {n : ℕ} {r0 : R} {r : Fin n → R}
    (hr : IsRightUnimodularCons r0 r) :
    IsRightUnimodularCons (f r0) (fun i ↦ f (r i)) := by
  obtain ⟨w0, w, hw⟩ := hr
  refine ⟨f w0, fun i ↦ f (w i), ?_⟩
  simpa using congrArg f hw

/-- Bass's stable-range condition is preserved by a ring equivalence. -/
theorem StableRangeCondition.map_equiv
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    {n : ℕ} (h : StableRangeCondition R n) (e : R ≃+* S) :
    StableRangeCondition S n := by
  intro r0 r hr
  have hr' := hr.map e.symm.toRingHom
  obtain ⟨t, w, hw⟩ := h (e.symm r0) (fun i ↦ e.symm (r i)) hr'
  refine ⟨fun i ↦ e (t i), fun i ↦ e (w i), ?_⟩
  simpa using congrArg e hw

/-- Bass's stable-range condition is invariant under ring equivalence. -/
theorem stableRangeCondition_equiv_iff
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (e : R ≃+* S) (n : ℕ) :
    StableRangeCondition R n ↔ StableRangeCondition S n :=
  ⟨fun h ↦ h.map_equiv e, fun h ↦ h.map_equiv e.symm⟩

/-- Vaserstein's one-step implication: `(S_n)` implies `(S_(n+1))`;
see Weibel, *The K-book*, Exercise I.1.5(a). -/
theorem stableRangeCondition_succ {R : Type u} [Ring R] (n : ℕ) :
    StableRangeCondition R n → StableRangeCondition R (n + 1) := by
  intro hn r0 r hr
  obtain ⟨b0, b, hb⟩ := hr
  let r1 : R := r 0
  let tail : Fin n → R := fun i ↦ r i.succ
  let b1 : R := b 0
  let btail : Fin n → R := fun i ↦ b i.succ
  let c : R := r0 * b0 + r1 * b1
  have hc : IsRightUnimodularCons c tail := by
    refine ⟨1, btail, ?_⟩
    simpa [c, r1, b1, tail, btail, Fin.sum_univ_succ, add_assoc] using hb
  obtain ⟨t, w, hw⟩ := hn c tail hc
  let q : R := ∑ i, (b1 * t i) * w i
  refine ⟨Fin.cases 0 (fun i ↦ b0 * t i), ?_⟩
  refine ⟨Fin.cases (-q) w, ?_⟩
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, mul_zero, sub_zero]
  calc
    r 0 * -q + ∑ i, (r i.succ - r0 * (b0 * t i)) * w i =
        ∑ i, (tail i - c * t i) * w i := by
      simp only [tail, c, r1, b1, q, sub_mul, add_mul, mul_assoc,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, mul_neg]
      abel
    _ = 1 := hw

/-- The stable-range conditions are monotone in their index. -/
theorem stableRangeCondition_mono {R : Type u} [Ring R] {m n : ℕ}
    (hmn : m ≤ n) : StableRangeCondition R m → StableRangeCondition R n := by
  intro hm
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ n _ ih => exact stableRangeCondition_succ n ih

/-- `s` is the least natural index satisfying Bass's stable-range condition.

This relational formulation does not assign a default natural number to a ring
for which no finite stable range has been supplied; compare Weibel,
*The K-book*, Exercise I.1.5. -/
def IsStableRange (R : Type u) [Ring R] (s : ℕ) : Prop :=
  StableRangeCondition R s ∧ ∀ m, StableRangeCondition R m → s ≤ m

/-- Every condition whose index is at least a supplied least stable range
holds. -/
theorem stableRangeCondition_of_isStableRange
    {R : Type u} [Ring R] {s n : ℕ}
    (hs : IsStableRange R s) (hsn : s ≤ n) : StableRangeCondition R n :=
  stableRangeCondition_mono hsn hs.1

end Bass
