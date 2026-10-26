/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.FiniteIntersections.PrimeIdeals
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import SpectralStoneDuality.Topology.GenericPoint

/-!
# Spectra of finite intersections of valuation rings

A finite pointwise rank-at-most-one intersection has a finite spectrum whose
open sets are precisely the empty set and the subsets containing the zero prime.
For pairwise inequivalent nontrivial rank-one places, its spectrum has the
topology of a fork: a generic point below one closed point for each place.
The fork is `Topology.WithGenericPoint` from Spectral Stone Duality; the
previous `Topology.GenericFork` names remain as deprecated aliases. Its point
map is a homeomorphism onto the spectrum.

The finite rank-at-most-one and empty/trivial-place cases extend beyond the
finite nontrivial rank-one strategy cited below. The homeomorphism concerns
only a spectrum, not a representation of a source topological space.

## References

* Mathlib contributors: prime-spectrum specialization, finite Alexandrov
  spaces and lower-set topologies.
* Formal Frontier Agents, `SpectralStoneDuality.Topology.GenericPoint`:
  the reusable generic-point fork and its order and topology.
* Formal Frontier Agents, `ValuationIntegers.FiniteIntersections.PrimeIdeals`:
  the finite-family prime classification and dimension bound reused below.
* Stefan Schröer, *A simple proof for Hochster's Theorem*, §2: the finite-space
  valuation strategy, with antecedent credit to Y. Ershov conveyed through
  Schröer. Ershov's original text is not used here.
-/

@[expose] public section

universe u v w

namespace Topology

/-- The former name for a generic point with independently indexed closed points.
Use `WithGenericPoint` directly in new developments. -/
@[deprecated WithGenericPoint (since := "2026-10-07")]
abbrev GenericFork (ι : Type v) : Type v := WithGenericPoint ι

namespace GenericFork

variable {ι : Type v}

/-- The old constructor for the unique generic point. -/
@[match_pattern, deprecated WithGenericPoint.generic (since := "2026-10-07")]
abbrev generic : WithGenericPoint ι := WithGenericPoint.generic

/-- The old constructor for an indexed closed point. -/
@[match_pattern, deprecated WithGenericPoint.closed (since := "2026-10-07")]
abbrev closed (i : ι) : WithGenericPoint ι := WithGenericPoint.closed i

@[deprecated (since := "2026-10-07")] noncomputable alias rec := WithGenericPoint.rec
@[deprecated (since := "2026-10-07")] noncomputable alias recOn := WithGenericPoint.recOn
@[deprecated (since := "2026-10-07")] alias casesOn := WithGenericPoint.casesOn
@[deprecated (since := "2026-10-07")]
noncomputable alias noConfusion := WithGenericPoint.noConfusion
@[deprecated (since := "2026-10-07")] alias noConfusionType := WithGenericPoint.noConfusionType
@[deprecated (since := "2026-10-07")] alias ctorIdx := WithGenericPoint.ctorIdx
@[deprecated (since := "2026-10-07")] alias ctorElim := WithGenericPoint.ctorElim
@[deprecated (since := "2026-10-07")] alias ctorElimType := WithGenericPoint.ctorElimType
@[deprecated (since := "2026-10-07")]
noncomputable alias _sizeOf_inst := WithGenericPoint._sizeOf_inst
@[deprecated (since := "2026-10-07")]
alias instPartialOrder := WithGenericPoint.instPartialOrder
@[deprecated (since := "2026-10-07")]
alias instTopologicalSpace := WithGenericPoint.instTopologicalSpace

namespace generic

@[deprecated (since := "2026-10-07")] alias elim := WithGenericPoint.generic.elim
@[deprecated (since := "2026-10-07")]
alias sizeOf_spec := WithGenericPoint.generic.sizeOf_spec

end generic

namespace closed

@[deprecated (since := "2026-10-07")] alias elim := WithGenericPoint.closed.elim
@[deprecated (since := "2026-10-07")] alias inj := WithGenericPoint.closed.inj
@[deprecated (since := "2026-10-07")] alias injEq := WithGenericPoint.closed.injEq
@[deprecated (since := "2026-10-07")]
alias noConfusion := WithGenericPoint.closed.noConfusion
@[deprecated (since := "2026-10-07")]
alias sizeOf_spec := WithGenericPoint.closed.sizeOf_spec

end closed

@[deprecated (since := "2026-10-07")] alias isOpen_iff := WithGenericPoint.isOpen_iff
@[deprecated (since := "2026-10-07")]
alias generic_specializes := WithGenericPoint.generic_specializes
@[deprecated (since := "2026-10-07")] alias closed_isClosed := WithGenericPoint.closed_isClosed
@[deprecated (since := "2026-10-07")]
alias closed_specializes_closed_iff := WithGenericPoint.closed_specializes_closed_iff

end GenericFork

end Topology

namespace PrimeSpectrum

variable (R : Type u) [CommRing R] [IsDomain R]

/-- For a finite one-dimensional domain spectrum, openness is equivalent to
containing the zero prime, except for the empty open set. The dimension bound
is essential: in a three-prime chain, a set containing the bottom and top
but omitting the intermediate prime is not open. -/
theorem isOpen_iff_eq_empty_or_bot_mem [Finite (PrimeSpectrum R)]
    [Ring.KrullDimLE 1 R] (s : Set (PrimeSpectrum R)) :
    IsOpen s ↔ s = ∅ ∨ (⊥ : PrimeSpectrum R) ∈ s := by
  constructor
  · intro hs
    by_cases h : s = ∅
    · exact Or.inl h
    · right
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr h
      exact (specializes_iff_forall_open.mp
        ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)) s hs hp
  · rintro (rfl | hbot)
    · exact isOpen_empty
    · have hclosed : IsClosed (sᶜ) := by
        have hclosed' : IsClosed
            (⋃ p : {p : PrimeSpectrum R // p ∉ s}, {p.1}) := by
          apply isClosed_iUnion
          intro p
          apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p.1).mpr
          apply Ideal.IsPrime.isMaximal_of_ne_bot p.1.isPrime
          intro h
          have hp : p.1 = ⊥ := PrimeSpectrum.ext (by simpa using h)
          exact p.2 (hp ▸ hbot)
        convert hclosed' using 1
        ext p
        simp
      exact isClosed_compl_iff.mp hclosed

end PrimeSpectrum

namespace Valuation

variable {K : Type u} [Field K] {ι : Type v} {Γ₀ : Type w}
  [LinearOrderedCommGroupWithZero Γ₀] (val : ι → Valuation K Γ₀)

section FiniteRankLeOne

variable [Finite ι] [∀ i, (val i).RankLeOne]

/-- Every prime of the intersection is either zero or contracted from one
place, so the spectrum is finite even with empty, repeated or trivial places. -/
noncomputable instance : Finite (PrimeSpectrum (intersectionSubring val)) := by
  let point : Option ι → PrimeSpectrum (intersectionSubring val) :=
    fun x => match x with
    | none => ⊥
    | some i => ⟨contractedIdeal val i, inferInstance⟩
  refine Finite.of_surjective point ?_
  intro p
  rcases (isPrime_iff_eq_bot_or_contractedIdeal val p.asIdeal).mp p.isPrime with
    hzero | ⟨i, hi⟩
  · exact ⟨none, PrimeSpectrum.ext hzero.symm⟩
  · exact ⟨some i, PrimeSpectrum.ext hi.symm⟩

/-- The nonempty Zariski opens of a finite rank-at-most-one intersection
contain its zero prime, also for empty, mixed and repeated families. -/
theorem isOpen_iff_eq_empty_or_bot_mem
    (s : Set (PrimeSpectrum (intersectionSubring val))) :
    IsOpen s ↔ s = ∅ ∨ (⊥ : PrimeSpectrum (intersectionSubring val)) ∈ s :=
  PrimeSpectrum.isOpen_iff_eq_empty_or_bot_mem _ s

end FiniteRankLeOne

section PairwiseInequivalent

/-- The fork's generic point maps to zero, and its indexed closed points
map to the contracted maximal ideals. -/
noncomputable def forkPoint : Topology.WithGenericPoint ι → PrimeSpectrum (intersectionSubring val)
  | .generic => ⊥
  | .closed i => ⟨contractedIdeal val i, inferInstance⟩

@[simp]
theorem forkPoint_generic :
    forkPoint val Topology.WithGenericPoint.generic = (⊥ : PrimeSpectrum _) := rfl

@[simp]
theorem forkPoint_closed (i : ι) :
    forkPoint val (Topology.WithGenericPoint.closed i) =
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) := rfl

/-- Pairwise inequivalence and nontriviality make the generic and indexed
contracted primes distinct, with no other prime points. -/
theorem forkPoint_bijective [Finite ι] [∀ i, (val i).RankOne]
    (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j)) :
    Function.Bijective (forkPoint val) := by
  constructor
  · intro x y hxy
    cases x with
    | generic =>
      cases y with
      | generic => rfl
      | closed j =>
        have hbot : contractedIdeal val j = ⊥ :=
          (congrArg PrimeSpectrum.asIdeal hxy).symm
        exact ((contractedIdeal_eq_bot_iff val j).mp hbot
          (inferInstance : (val j).IsNontrivial)).elim
    | closed i =>
      cases y with
      | generic =>
        have hbot : contractedIdeal val i = ⊥ :=
          congrArg PrimeSpectrum.asIdeal hxy
        exact ((contractedIdeal_eq_bot_iff val i).mp hbot
          (inferInstance : (val i).IsNontrivial)).elim
      | closed j =>
        exact congrArg Topology.WithGenericPoint.closed
          (contractedIdeal_injective val hindep (congrArg PrimeSpectrum.asIdeal hxy))
  · intro p
    rcases (isPrime_iff_eq_bot_or_contractedIdeal val p.asIdeal).mp p.isPrime with
      hbot | ⟨i, hi⟩
    · refine ⟨.generic, ?_⟩
      apply PrimeSpectrum.ext
      simpa using hbot.symm
    · refine ⟨.closed i, ?_⟩
      apply PrimeSpectrum.ext
      simpa using hi.symm

/-- The spectrum of a finite pairwise inequivalent nontrivial rank-one family
is homeomorphic to its independent generic-point fork. -/
noncomputable def forkHomeomorph [Finite ι] [∀ i, (val i).RankOne]
    (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j)) :
    Topology.WithGenericPoint ι ≃ₜ PrimeSpectrum (intersectionSubring val) :=
  (Equiv.ofBijective (forkPoint val) (forkPoint_bijective val hindep)).toHomeomorph
    (by
      intro s
      have hempty : (forkPoint val ⁻¹' s) = ∅ ↔ s = ∅ := by
        constructor
        · intro h
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro p hp
          obtain ⟨x, rfl⟩ := (forkPoint_bijective val hindep).2 p
          have hx : x ∈ forkPoint val ⁻¹' s := hp
          simp only [h, Set.mem_empty_iff_false] at hx
        · rintro rfl
          rfl
      rw [Topology.WithGenericPoint.isOpen_iff,
        PrimeSpectrum.isOpen_iff_eq_empty_or_bot_mem]
      change (forkPoint val ⁻¹' s = ∅ ∨
        Topology.WithGenericPoint.generic ∈ forkPoint val ⁻¹' s) ↔
          s = ∅ ∨ (⊥ : PrimeSpectrum (intersectionSubring val)) ∈ s
      rw [hempty]
      simp only [Set.mem_preimage, forkPoint_generic])

variable [Finite ι] [∀ i, (val i).RankOne]
  (hindep : Pairwise fun i j => ¬(val i).IsEquiv (val j))

@[simp]
theorem forkHomeomorph_generic :
    forkHomeomorph val hindep Topology.WithGenericPoint.generic =
      (⊥ : PrimeSpectrum _) := rfl

@[simp]
theorem forkHomeomorph_closed (i : ι) :
    forkHomeomorph val hindep (Topology.WithGenericPoint.closed i) =
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) := rfl

@[simp]
theorem forkHomeomorph_symm_bot :
    (forkHomeomorph val hindep).symm (⊥ : PrimeSpectrum _) =
      Topology.WithGenericPoint.generic := by
  apply (forkHomeomorph val hindep).injective
  simp

@[simp]
theorem forkHomeomorph_symm_contractedIdeal (i : ι) :
    (forkHomeomorph val hindep).symm
      (⟨contractedIdeal val i, inferInstance⟩ : PrimeSpectrum _) =
      Topology.WithGenericPoint.closed i := by
  apply (forkHomeomorph val hindep).injective
  simp

end PairwiseInequivalent

end Valuation
