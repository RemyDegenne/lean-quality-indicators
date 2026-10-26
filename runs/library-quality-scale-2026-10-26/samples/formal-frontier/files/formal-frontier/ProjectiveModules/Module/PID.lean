/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Arbitrary-rank free and projective modules over a PID

This file removes the finite-generation restriction from the usual freeness
theorems over a commutative principal ideal domain.

## Main results

* `Submodule.free_of_pid_of_free`: every submodule of an arbitrary-rank free
  module over a commutative PID is free.
* `Module.Projective.free_of_pid`: every arbitrary-rank projective module over
  a commutative PID is free.

## Construction

Choose and well-order a basis of the ambient free module.  For each basis
index `i`, consider the ideal of possible `i`-coordinates of elements of the
submodule whose later coordinates vanish.  Choose a vector over a generator
when this ideal is nonzero.  The resulting family is triangular, hence
linearly independent over the domain.  It spans by well-founded induction:
subtract the selected vector at the largest nonzero coordinate, whose
existence follows from finite support.

This proof uses no finite-generation, cardinality, countability, or
decidability hypothesis on the module or on a basis index type.
-/

@[expose] public section

noncomputable section

open Module Submodule.IsPrincipal

namespace Submodule.PIDFree

universe u v w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M]
variable (b : Basis ι R M)

local instance : LinearOrder ι := WellOrderingRel.isWellOrder.linearOrder
local instance : WellFoundedLT ι := ⟨WellOrderingRel.isWellOrder.wf⟩

/-- Vectors whose basis coordinates strictly after `i` vanish. -/
private def upTo (i : ι) : Submodule R M :=
  ⨅ j : {j : ι // i < j}, LinearMap.ker (b.coord j)

omit [IsDomain R] [IsPrincipalIdealRing R] in
private lemma mem_upTo_iff {i : ι} {x : M} :
    x ∈ upTo b i ↔ ∀ j, i < j → b.coord j x = 0 := by
  simp [upTo]

variable (N : Submodule R M)

/-- The ideal of possible leading coordinates at `i`. -/
private def leadingIdeal (i : ι) : Ideal R :=
  (N ⊓ upTo b i).map (b.coord i)

/-- A submodule vector realizing the chosen generator of the leading ideal. -/
private def leadingVector (i : ι) : M :=
  Classical.choose ((Submodule.mem_map).mp
    (generator_mem (leadingIdeal b N i)))

omit [IsDomain R] in
private lemma leadingVector_mem (i : ι) : leadingVector b N i ∈ N ⊓ upTo b i :=
  (Classical.choose_spec ((Submodule.mem_map).mp
    (generator_mem (leadingIdeal b N i)))).1

omit [IsDomain R] in
private lemma coord_leadingVector (i : ι) :
    b.coord i (leadingVector b N i) = generator (leadingIdeal b N i) :=
  (Classical.choose_spec ((Submodule.mem_map).mp
    (generator_mem (leadingIdeal b N i)))).2

/-- Basis indices whose leading-coordinate ideal is nonzero. -/
private def ActiveIndex :=
  {i : ι // generator (leadingIdeal b N i) ≠ 0}

/-- The triangular family selected from the submodule. -/
private def leadingFamily (i : ActiveIndex b N) : N :=
  ⟨leadingVector b N i.1, (leadingVector_mem b N i.1).1⟩

omit [IsDomain R] in
private lemma leadingFamily_mem_upTo (i : ActiveIndex b N) :
    (leadingFamily b N i : M) ∈ upTo b i.1 :=
  (leadingVector_mem b N i.1).2

omit [IsDomain R] in
private lemma coord_leadingFamily_self (i : ActiveIndex b N) :
    b.coord i.1 (leadingFamily b N i) = generator (leadingIdeal b N i.1) :=
  coord_leadingVector b N i.1

omit [IsDomain R] in
private lemma coord_leadingFamily_of_lt (i : ActiveIndex b N) {j : ι}
    (hij : i.1 < j) : b.coord j (leadingFamily b N i) = 0 :=
  (mem_upTo_iff b).mp (leadingFamily_mem_upTo b N i) j hij

private lemma leadingFamily_linearIndependent :
    LinearIndependent R (leadingFamily b N) := by
  let _ : LinearOrder (ActiveIndex b N) := Subtype.instLinearOrder
    (fun i : ι ↦ generator (leadingIdeal b N i) ≠ 0)
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let t := s.filter fun j ↦ g j ≠ 0
  have hit : i ∈ t := Finset.mem_filter.mpr ⟨hi, hgi⟩
  have ht : t.Nonempty := ⟨i, hit⟩
  let k := t.max' ht
  have hkt : k ∈ t := t.max'_mem ht
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hkg : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hcoord := congrArg
    (fun x : N ↦ ((b.coord k.1).comp N.subtype) x) hsum
  simp only [map_sum, map_smul, map_zero] at hcoord
  have hcollapse :
      ∑ j ∈ s, g j • b.coord k.1 (leadingFamily b N j) =
        g k • b.coord k.1 (leadingFamily b N k) := by
    apply Finset.sum_eq_single k
    · intro j hjs hjk
      by_cases hgj : g j = 0
      · simp [hgj]
      · have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hjs, hgj⟩
        have hjle : j ≤ k := t.le_max' j hjt
        have hjle' : j.1 ≤ k.1 := Subtype.coe_le_coe.mpr hjle
        have hne : j.1 ≠ k.1 := fun h ↦ hjk (Subtype.ext h)
        have hjlt : j.1 < k.1 := lt_of_le_of_ne hjle' hne
        rw [coord_leadingFamily_of_lt b N j hjlt, smul_zero]
    · exact fun hk ↦ (hk hks).elim
  have hprod : g k * generator (leadingIdeal b N k.1) = 0 := by
    rw [← smul_eq_mul, ← coord_leadingFamily_self b N k, ← hcollapse]
    exact hcoord
  exact k.2 ((mul_eq_zero.mp hprod).resolve_left hkg)

omit [IsDomain R] in
private lemma leadingFamily_spans :
    ⊤ ≤ Submodule.span R (Set.range (leadingFamily b N)) := by
  let S := Submodule.span R (Set.range (leadingFamily b N))
  have h_upTo : ∀ i : ι, ∀ x : N, (x : M) ∈ upTo b i → x ∈ S := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro x hx
      have lower_span : ∀ z : N, (z : M) ∈ upTo b i → b.coord i z = 0 → z ∈ S := by
        intro z hz_up hz_coord
        by_cases hz0 : z = 0
        · subst z
          exact S.zero_mem
        · have hzval : (z : M) ≠ 0 := fun h ↦ hz0 (Subtype.ext h)
          have hzrepr : b.repr (z : M) ≠ 0 := by
            intro h
            apply hzval
            apply b.repr.injective
            simpa using h
          have hsupp : (b.repr (z : M)).support.Nonempty :=
            Finsupp.support_nonempty_iff.mpr hzrepr
          let j := (b.repr (z : M)).support.max' hsupp
          have hjmem : j ∈ (b.repr (z : M)).support :=
            (b.repr (z : M)).support.max'_mem hsupp
          have hjle : j ≤ i := by
            apply (b.repr (z : M)).support.max'_le
            intro k hk
            apply le_of_not_gt
            intro hik
            have hkzero := (mem_upTo_iff b).mp hz_up k hik
            have hkne : b.coord k (z : M) ≠ 0 := by
              simpa using (Finsupp.mem_support_iff.mp hk)
            exact hkne hkzero
          have hjne : j ≠ i := by
            intro hji
            have hjcoord : b.coord j (z : M) ≠ 0 := by
              simpa using (Finsupp.mem_support_iff.mp hjmem)
            exact hjcoord (hji ▸ hz_coord)
          have hji : j < i := lt_of_le_of_ne hjle hjne
          apply ih j hji z
          rw [mem_upTo_iff]
          intro k hjk
          have hknot : k ∉ (b.repr (z : M)).support := by
            intro hk
            exact (not_lt_of_ge ((b.repr (z : M)).support.le_max' k hk)) hjk
          simpa using (Finsupp.notMem_support_iff.mp hknot)
      have hxideal : b.coord i x ∈ leadingIdeal b N i := by
        rw [leadingIdeal, Submodule.mem_map]
        exact ⟨(x : M), ⟨x.2, hx⟩, rfl⟩
      obtain ⟨r, hr⟩ :=
        (mem_iff_eq_smul_generator (leadingIdeal b N i)).mp hxideal
      by_cases ha : generator (leadingIdeal b N i) = 0
      · apply lower_span x hx
        rw [hr, ha, smul_zero]
      · let a : ActiveIndex b N := ⟨i, ha⟩
        let y : N := x - r • leadingFamily b N a
        have hy_up : (y : M) ∈ upTo b i := by
          exact Submodule.sub_mem _ hx
            (Submodule.smul_mem _ r (leadingFamily_mem_upTo b N a))
        have hy_coord : b.coord i y = 0 := by
          calc
            b.coord i y = b.coord i x - r • b.coord i (leadingFamily b N a) := by
              simp [y]
            _ = r • generator (leadingIdeal b N i) -
                r • generator (leadingIdeal b N i) := by
              rw [hr, coord_leadingFamily_self b N a]
            _ = 0 := sub_self _
        have hyS : y ∈ S := lower_span y hy_up hy_coord
        have haS : leadingFamily b N a ∈ S :=
          Submodule.subset_span (Set.mem_range_self a)
        have hxy : x = y + r • leadingFamily b N a := by
          simp [y]
        rw [hxy]
        exact S.add_mem hyS (S.smul_mem r haS)
  intro x _
  by_cases hx0 : x = 0
  · subst x
    exact S.zero_mem
  · have hxval : (x : M) ≠ 0 := fun h ↦ hx0 (Subtype.ext h)
    have hxrepr : b.repr (x : M) ≠ 0 := by
      intro h
      apply hxval
      apply b.repr.injective
      simpa using h
    have hsupp : (b.repr (x : M)).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr hxrepr
    let i := (b.repr (x : M)).support.max' hsupp
    apply h_upTo i x
    rw [mem_upTo_iff]
    intro j hij
    have hjnot : j ∉ (b.repr (x : M)).support := by
      intro hj
      exact (not_lt_of_ge ((b.repr (x : M)).support.le_max' j hj)) hij
    simpa using (Finsupp.notMem_support_iff.mp hjnot)

private def submoduleBasis : Basis (ActiveIndex b N) R N :=
  Basis.mk (leadingFamily_linearIndependent b N) (leadingFamily_spans b N)

end Submodule.PIDFree

namespace Submodule

universe u v

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M]

/-- Every submodule of an arbitrary-rank free module over a commutative PID is free. -/
theorem free_of_pid_of_free [Module.Free R M] (N : Submodule R M) : Module.Free R N := by
  let b := Module.Free.chooseBasis R M
  exact Module.Free.of_basis (PIDFree.submoduleBasis b N)

end Submodule

namespace Module.Projective

universe u v

variable (R : Type u) (P : Type v)
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup P] [Module R P] [Module.Projective R P]

/-- An arbitrary-rank projective module over a commutative PID is free. -/
theorem free_of_pid : Module.Free R P := by
  obtain ⟨M, _, _, _, i, s, hs⟩ :=
    (Module.Projective.iff_split (R := R) (P := P)).mp inferInstance
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  have hi : Function.Injective i := by
    intro x y hxy
    have h := congrArg s hxy
    simpa [← LinearMap.comp_apply, hs] using h
  exact Module.Free.of_equiv'
    (Submodule.free_of_pid_of_free (R := R) (M := M) (LinearMap.range i))
    (LinearEquiv.ofInjective i hi).symm

end Module.Projective
