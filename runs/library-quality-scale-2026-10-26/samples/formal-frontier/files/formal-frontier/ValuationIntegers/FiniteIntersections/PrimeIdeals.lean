/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections
public import ValuationIntegers.RankLeOneDimension

/-!
# Prime ideals of finite intersections of valuation rings

For a nonempty finite family, every maximal ideal of the intersection is a
contracted ideal, without a rank restriction; a contracted ideal need not be
maximal at higher rank. For a finite pointwise rank-at-most-one family, every
prime ideal is zero or a contracted ideal. At a selected place, a contracted
ideal is maximal exactly when either every place is trivial or the selected
valuation is nontrivial. In the all-trivial case the intersection is a field
and each contracted ideal is zero; in a mixed family a trivial place contracts
to zero, which is not maximal. The zero ideal is also maximal for the empty
family, which has no contracted ideals. These classification and dimension
statements hold without pairwise independence or discreteness assumptions.

## References

* [Mathlib contributors](https://github.com/leanprover-community/mathlib4):
  valuation subrings, localization, finite prime avoidance and dimension APIs.
* Fujiwara--Kato, *Foundations of Rigid Geometry I*, Remark 2.2.4(2):
  motivation for finite valuation intersections, not the exact results below.
* Stefan Schröer, *A simple proof for Hochster's Theorem*, §2: the finite-space
  valuation strategy. Schröer credits Y. Ershov for an antecedent strategy;
  Ershov's original text is not used here.

The published finite nontrivial rank-one argument motivates the classification.
The pointwise rank-at-most-one, trivial-place and empty-family generalizations
below are not stated in these sources.
-/

@[expose] public section

universe u v w

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

section FiniteNonempty

variable [Finite ι] [Nonempty ι]

/-- For a nonempty finite family, every maximal ideal of the intersection is
contracted from a place, without a rank or independence assumption. This
rank-free enumeration extends the finite-space strategy of Stefan Schröer,
*A simple proof for Hochster's Theorem*, §2. -/
theorem exists_contractedIdeal_of_isMaximal
    {M : Ideal (intersectionSubring val)} (hM : M.IsMaximal) :
    ∃ i, M = contractedIdeal val i := by
  classical
  have hcover : (M : Set (intersectionSubring val)) ⊆
      ⋃ i ∈ (Set.univ : Set ι), (contractedIdeal val i : Set (intersectionSubring val)) := by
    intro x hx
    by_contra h
    have hnot (i : ι) : x ∉ contractedIdeal val i := by
      intro hxi
      apply h
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Set.mem_univ i, hxi⟩⟩
    have hx0 : (x : K) ≠ 0 := by
      intro hzero
      apply hnot (Classical.choice ‹Nonempty ι›)
      have : x = 0 := Subtype.ext hzero
      simp [this]
    have hunit : IsUnit x := (isUnit_intersectionSubring_iff val x).mpr
      ⟨hx0, fun i => le_antisymm
        ((mem_intersectionSubring_iff val _).mp x.property i)
        (le_of_not_gt (fun hlt => hnot i ((mem_contractedIdeal_iff val i x).mpr hlt)))⟩
    exact hM.ne_top (M.eq_top_of_isUnit_mem hx hunit)
  let chosen : ι := Classical.choice ‹Nonempty ι›
  obtain ⟨i, _, hle⟩ := (Ideal.subset_union_prime_finite Set.finite_univ
    chosen chosen (fun i _ _ _ => inferInstance)).mp hcover
  exact ⟨i, hM.eq_of_le (inferInstance : (contractedIdeal val i).IsPrime).ne_top hle⟩

end FiniteNonempty

section FiniteRankLeOne

variable [Finite ι] [∀ i, (val i).RankLeOne]

/-- The contracted prime at a selected place is zero exactly when that
valuation is trivial. Repeated places need not have distinct contracted ideals.
The trivial-place case is beyond the nontrivial rank-one setting of Schröer, §2. -/
theorem contractedIdeal_eq_bot_iff (i : ι) :
    contractedIdeal val i = ⊥ ↔ ¬(val i).IsNontrivial := by
  constructor
  · intro hbot hi
    obtain ⟨x, hx0, hxlt⟩ := (val i).isNontrivial_iff_exists_lt_one.mp hi
    let b : (val i).valuationSubring :=
      ⟨x, ((val i).mem_valuationSubring_iff x).mpr hxlt.le⟩
    obtain ⟨a, s, hs, heq⟩ := exists_fraction_at_contractedIdeal val i b
    have hab : (a : K) = (s : K) * x := by
      simpa only [b] using heq
    have hs0 : (s : K) ≠ 0 := by
      intro hzero
      apply hs
      exact (mem_contractedIdeal_iff val i s).mpr (by simp [hzero])
    have ha0 : (a : K) ≠ 0 := by
      rw [hab]
      exact mul_ne_zero hs0 hx0
    have ha : a ∈ contractedIdeal val i := (mem_contractedIdeal_iff val i a).mpr (by
      rw [hab, map_mul]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right
          ((mem_intersectionSubring_iff val _).mp s.property i) (zero_le (a := val i x)))
        (by simpa only [one_mul] using hxlt))
    have : a = 0 := by simpa only [hbot, Ideal.mem_bot] using ha
    exact ha0 (congrArg (fun y : intersectionSubring val => (y : K)) this)
  · intro htriv
    apply le_antisymm _ bot_le
    intro x hx
    have hx0 : (x : K) = 0 := by
      by_contra hnonzero
      exact htriv ((val i).isNontrivial_iff_exists_lt_one.mpr
        ⟨x, hnonzero, (mem_contractedIdeal_iff val i x).mp hx⟩)
    exact (Ideal.mem_bot).mpr (Subtype.ext hx0)

/-- The intersection is a field exactly when every valuation in the finite
family is trivial; the empty family is included. These cases extend beyond
the finite nontrivial rank-one setting of Schröer, §2. -/
theorem isField_intersectionSubring_iff :
    IsField (intersectionSubring val) ↔ ∀ i, ¬(val i).IsNontrivial := by
  constructor
  · intro hfield i hi
    have hne : contractedIdeal val i ≠ ⊥ := by
      intro hzero
      exact (contractedIdeal_eq_bot_iff val i).mp hzero hi
    exact (Ring.not_isField_of_ne_of_ne hne
      (inferInstance : (contractedIdeal val i).IsPrime).ne_top) hfield
  · intro htriv
    refine ⟨exists_pair_ne _, mul_comm, ?_⟩
    intro x hx
    have hx0 : (x : K) ≠ 0 := by
      intro hzero
      apply hx
      exact Subtype.ext hzero
    apply isUnit_iff_exists_inv.mp
    apply (isUnit_intersectionSubring_iff val x).mpr
    refine ⟨hx0, fun i => le_antisymm
      ((mem_intersectionSubring_iff val _).mp x.property i) ?_⟩
    apply le_of_not_gt
    intro hlt
    exact htriv i ((val i).isNontrivial_iff_exists_lt_one.mpr ⟨x, hx0, hlt⟩)

private theorem nonempty_of_isPrime_ne_bot
    (P : Ideal (intersectionSubring val)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Nonempty ι := by
  by_contra hempty
  have htriv : ∀ i, ¬(val i).IsNontrivial := fun i => (hempty ⟨i⟩).elim
  exact (Ring.not_isField_of_ne_of_ne hP0 hP.ne_top)
    ((isField_intersectionSubring_iff val).mpr htriv)

private theorem isMaximal_of_isPrime_ne_bot
    (P : Ideal (intersectionSubring val)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P.IsMaximal := by
  classical
  have hnonempty := nonempty_of_isPrime_ne_bot val P hP hP0
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  obtain ⟨i, rfl⟩ := exists_contractedIdeal_of_isMaximal val hM
  let equivalence := IsLocalization.AtPrime.orderIsoOfPrime
    (val i).valuationSubring (contractedIdeal val i)
  let Q := equivalence.symm ⟨P, hP, hPM⟩
  have hQunder : Q.val.under (intersectionSubring val) = P := by
    have heq := congrArg Subtype.val
      (equivalence.apply_symm_apply (⟨P, hP, hPM⟩ :
        { J : Ideal (intersectionSubring val) // J.IsPrime ∧ J ≤ contractedIdeal val i }))
    change Q.val.under (intersectionSubring val) = P at heq
    exact heq
  have hQ0 : Q.val ≠ ⊥ := by
    intro hbot
    apply hP0
    have hlocal : Function.Injective
        (algebraMap (intersectionSubring val) (val i).valuationSubring) :=
      intersectionInclusion_injective val i
    rw [← hQunder, hbot]
    exact Ideal.comap_bot_of_injective _ hlocal
  have hdim : Ring.KrullDimLE 1 (val i).valuationSubring :=
    Valuation.Integers.krullDimLE_one (Valuation.valuationSubring.integers (val i))
  have hQmax : Q.val.IsMaximal := Q.property.isMaximal_of_ne_bot hQ0
  have hPM' : P = contractedIdeal val i := by
    calc
      P = Q.val.under (intersectionSubring val) := hQunder.symm
      _ = (IsLocalRing.maximalIdeal (val i).valuationSubring).under
          (intersectionSubring val) := congrArg
            (fun J : Ideal (val i).valuationSubring => J.under (intersectionSubring val))
            (IsLocalRing.eq_maximalIdeal hQmax)
      _ = contractedIdeal val i := IsLocalization.AtPrime.under_maximalIdeal _ _
  exact hPM' ▸ hM

/-- Every prime of a finite rank-at-most-one intersection is zero or the
contraction of a valuation's maximal ideal, including for an empty family.
The finite nontrivial rank-one strategy follows Stefan Schröer,
*A simple proof for Hochster's Theorem*, §2; Fujiwara--Kato,
*Foundations of Rigid Geometry I*, Remark 2.2.4(2), motivates the finite
intersection. Neither source states this empty/trivial-place generalization. -/
theorem isPrime_iff_eq_bot_or_contractedIdeal
    (P : Ideal (intersectionSubring val)) :
    P.IsPrime ↔ P = ⊥ ∨ ∃ i, P = contractedIdeal val i := by
  classical
  constructor
  · intro hP
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    · right
      have hne : Nonempty ι := nonempty_of_isPrime_ne_bot val P hP hbot
      exact exists_contractedIdeal_of_isMaximal val
        (isMaximal_of_isPrime_ne_bot val P hP hbot)
  · rintro (rfl | ⟨i, rfl⟩)
    · infer_instance
    · infer_instance

/-- The zero ideal is maximal only in the all-trivial case; every other
maximal ideal comes from a nontrivial place. The finite nontrivial rank-one
strategy follows Schröer, *A simple proof for Hochster's Theorem*, §2;
the rank-at-most-one and empty/trivial-place cases are generalizations. -/
theorem isMaximal_iff_eq_bot_or_contractedIdeal
    (M : Ideal (intersectionSubring val)) :
    M.IsMaximal ↔
      (M = ⊥ ∧ ∀ i, ¬(val i).IsNontrivial) ∨
        ∃ i, (val i).IsNontrivial ∧ M = contractedIdeal val i := by
  classical
  constructor
  · intro hM
    by_cases htriv : ∀ i, ¬(val i).IsNontrivial
    · left
      have hfield := (isField_intersectionSubring_iff val).mpr htriv
      exact ⟨((Ring.isField_iff_maximal_bot.mp hfield).eq_of_le hM.ne_top bot_le).symm,
        htriv⟩
    · right
      have hne : Nonempty ι := by
        by_contra hempty
        exact htriv (fun i => (hempty ⟨i⟩).elim)
      obtain ⟨i, rfl⟩ := exists_contractedIdeal_of_isMaximal val hM
      refine ⟨i, ?_, rfl⟩
      by_contra hi
      have hbot := (contractedIdeal_eq_bot_iff val i).mpr hi
      exact htriv ((isField_intersectionSubring_iff val).mp
        (Ring.isField_iff_maximal_bot.mpr (hbot ▸ hM)))
  · rintro (⟨rfl, htriv⟩ | ⟨i, hi, rfl⟩)
    · exact Ring.isField_iff_maximal_bot.mp
        ((isField_intersectionSubring_iff val).mpr htriv)
    · let : (val i).IsNontrivial := hi
      exact contractedIdeal_isMaximal_of_rankLeOne val i

/-- Finite intersections of valuation rings of rank at most one have
Krull dimension at most one, even when the intersection is a field. This
extends the finite nontrivial rank-one argument of Schröer,
*A simple proof for Hochster's Theorem*, §2, using Mathlib's dimension APIs;
the empty/trivial-place cases are not stated there. -/
theorem krullDimLE_one : Ring.KrullDimLE 1 (intersectionSubring val) := by
  exact Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr
    (fun P hP0 hP => isMaximal_of_isPrime_ne_bot val P hP hP0)

instance : Ring.KrullDimLE 1 (intersectionSubring val) := krullDimLE_one val

end FiniteRankLeOne

end Valuation
