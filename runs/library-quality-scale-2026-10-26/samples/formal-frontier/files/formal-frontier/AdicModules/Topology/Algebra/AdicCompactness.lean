/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.UniformSpace.Cauchy

import GroupTheory.Topology.Algebra.Group.TotalBounded
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Compactness for a given adic uniform ring

The compactness criteria below concern the original commutative ring with its given
uniformity and the topology induced by that uniformity. The adic hypothesis is the
existing proposition `IsAdic I`; no replacement topology or completion is introduced.
Only left-additive-uniform compatibility is required.

The general criterion uses finiteness of every natural-power quotient, including the
zeroth power. For a finitely generated ideal, finiteness of the first quotient suffices.
Completeness means uniform completeness, not separated algebraic adic completeness.
Neither criterion assumes a separation axiom or that the ideal is proper.

## References

* Mathlib's adic topology development by Patrick Massot.
* Mathlib's uniform compactness and completeness interfaces by Johannes Hölzl.
* Mathlib's finiteness results for ideal-power quotients by Andrew Yang.
* The subgroup-basis total-boundedness criterion in
  `GroupTheory.Topology.Algebra.Group.TotalBounded`.
-/

@[expose] public section

universe u

namespace IsAdic

variable {R : Type u} [CommRing R] [UniformSpace R] [IsLeftUniformAddGroup R]

/-- A ring with its given adic uniformity is compact exactly when it is complete and
all its natural-power ideal quotients are finite. No separation hypothesis is needed. -/
theorem compactSpace_iff (I : Ideal R) (hI : IsAdic I) :
    CompactSpace R ↔ CompleteSpace R ∧ ∀ n : ℕ, Finite (R ⧸ I ^ n) := by
  have htb := hI.hasBasis_nhds_zero.totallyBounded_univ_iff_addSubgroup_finiteIndex
    (H := fun n : ℕ => (I ^ n).toAddSubgroup)
  constructor
  · intro hc
    letI : CompactSpace R := hc
    refine ⟨complete_of_compact, fun n => ?_⟩
    exact (AddSubgroup.finiteIndex_iff_finite_quotient
      (H := (I ^ n).toAddSubgroup)).1 (htb.1 isCompact_univ.totallyBounded n trivial)
  · rintro ⟨hc, hfinite⟩
    letI : CompleteSpace R := hc
    apply isCompact_univ_iff.1
    apply isCompact_iff_totallyBounded_isComplete.2
    refine ⟨htb.2 ?_, isComplete_univ⟩
    intro n _
    exact (AddSubgroup.finiteIndex_iff_finite_quotient
      (H := (I ^ n).toAddSubgroup)).2 (hfinite n)

/-- For a finitely generated ideal defining the given topology, compactness is equivalent
to uniform completeness and finiteness of the first quotient. -/
theorem compactSpace_iff_of_fg (I : Ideal R) (hI : IsAdic I) (hfg : I.FG) :
    CompactSpace R ↔ CompleteSpace R ∧ Finite (R ⧸ I) := by
  constructor
  · intro hc
    obtain ⟨hcomplete, hfinite⟩ := (compactSpace_iff I hI).1 hc
    exact ⟨hcomplete, by simpa only [pow_one] using hfinite 1⟩
  · rintro ⟨hcomplete, hfinite⟩
    letI : Finite (R ⧸ I) := hfinite
    exact (compactSpace_iff I hI).2
      ⟨hcomplete, fun n => Ideal.finite_quotient_pow hfg n⟩

end IsAdic
