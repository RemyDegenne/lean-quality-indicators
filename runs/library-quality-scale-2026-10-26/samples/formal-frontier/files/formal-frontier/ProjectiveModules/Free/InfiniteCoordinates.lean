/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Infinite free coordinates

Over a nontrivial semiring, the index types of two bases of the same module have
the same cardinality as soon as one is infinite. This does not require invariant
basis number: finite free modules over some noncommutative rings can have bases
of different finite cardinalities. For an infinite index type, a linear
equivalence of free coordinate modules therefore determines an equivalence of
their index types. The index equivalence chosen below is not required to send
one basis vector to the other.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I,
  Section 1 (motivation for infinite-basis cardinality).
* Mathlib, `Mathlib.LinearAlgebra.Basis.Cardinality` and
  `Mathlib.LinearAlgebra.Dimension.StrongRankCondition` (the maximal-independent
  cardinal bound and its use for infinite bases).
-/

@[expose] public section

noncomputable section

open Cardinal Module

universe u v w w'

variable {R : Type u} {M : Type v} [Semiring R] [Nontrivial R]
  [AddCommMonoid M] [Module R M] {ι : Type w} {κ : Type w'}

/-- Two bases of the same module have equal lifted cardinalities if the first
index type is infinite. This generalizes the infinite-basis assertion in
Weibel, *The K-book*, Chapter I, Section 1 to nontrivial semirings; it needs
neither invariant basis number nor commutativity of the scalars. -/
theorem mk_eq_mk_of_basis_of_infinite [Infinite ι]
    (b : Basis ι R M) (c : Basis κ R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #κ := by
  have hbc := infinite_basis_le_maximal_linearIndependent' b _ c.linearIndependent c.maximal
  obtain ⟨embedding⟩ := Cardinal.lift_mk_le'.mp hbc
  have : Infinite κ := Infinite.of_injective embedding embedding.injective
  have hcb := infinite_basis_le_maximal_linearIndependent' c _ b.linearIndependent b.maximal
  exact le_antisymm hbc hcb

namespace Module.Basis

/-- A choice of an equivalence between the indices of two bases when the first
index type is infinite. It is not in general a basis-vector-preserving map. -/
def indexEquivOfInfinite [Infinite ι] (b : Basis ι R M) (c : Basis κ R M) : ι ≃ κ :=
  (Cardinal.lift_mk_eq'.mp (mk_eq_mk_of_basis_of_infinite b c)).some

/-- The chosen index equivalence agrees with `Basis.indexEquiv` when invariant
basis number is available. -/
theorem indexEquivOfInfinite_eq_indexEquiv [Infinite ι] [InvariantBasisNumber R]
    (b : Basis ι R M) (c : Basis κ R M) :
    b.indexEquivOfInfinite c = b.indexEquiv c := by
  rfl

end Module.Basis

namespace Finsupp

/-- Free coordinate modules with an infinite first index are linearly
equivalent precisely when their index types are equivalent. -/
theorem nonempty_linearEquiv_iff_equiv [Infinite ι] :
    Nonempty ((ι →₀ R) ≃ₗ[R] (κ →₀ R)) ↔ Nonempty (ι ≃ κ) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨((Finsupp.basisSingleOne (R := R) (ι := ι)).map f).indexEquivOfInfinite
      (Finsupp.basisSingleOne (R := R) (ι := κ))⟩
  · rintro ⟨e⟩
    exact ⟨Finsupp.domLCongr e⟩

/-- An equivalent cardinal formulation of classification of infinite free
coordinate modules, valid when the index types inhabit different universes. -/
theorem nonempty_linearEquiv_iff_lift_mk_eq [Infinite ι] :
    Nonempty ((ι →₀ R) ≃ₗ[R] (κ →₀ R)) ↔
      Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #κ :=
  (nonempty_linearEquiv_iff_equiv (R := R) (ι := ι) (κ := κ)).trans
    (Cardinal.lift_mk_eq' (α := ι) (β := κ)).symm

/-- A free coordinate module on an infinite index cannot be linearly
equivalent to one on a finite index over a nontrivial semiring. -/
theorem not_nonempty_linearEquiv_of_infinite_finite [Infinite ι] [Finite κ] :
    ¬ Nonempty ((ι →₀ R) ≃ₗ[R] (κ →₀ R)) := by
  intro h
  obtain ⟨e⟩ := (nonempty_linearEquiv_iff_equiv (R := R) (ι := ι) (κ := κ)).mp h
  have : Finite ι := Finite.of_equiv κ e.symm
  exact not_finite ι

end Finsupp
