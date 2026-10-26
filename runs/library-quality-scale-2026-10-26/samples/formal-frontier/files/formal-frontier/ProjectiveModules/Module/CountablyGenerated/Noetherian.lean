/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Credit: Formal Frontier Agents (original proof and separate library adaptation); docs/CREDITS.md
module

public import ProjectiveModules.Module.CountablyGenerated
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Countably generated submodules over Noetherian rings
-/

@[expose] public section

universe u v

namespace Module.CountablyGenerated

/-- Every submodule of a countably generated module over a (possibly
noncommutative) Noetherian ring is countably generated. -/
theorem submodule_of_isNoetherianRing
    {R : Type u} {M : Type v} [Ring R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    (hM : Module.CountablyGenerated R M) (N : Submodule R M) :
    Module.CountablyGenerated R N := by
  classical
  obtain ⟨x, hx⟩ := hM
  let stage : ℕ → Submodule R M := fun n =>
    Submodule.span R (Set.range (fun i : Fin (n + 1) => x i.val))
  have stage_mono : Monotone stage := by
    intro n m hnm
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castLE (Nat.succ_le_succ hnm) i, rfl⟩
  have stage_top : (⨆ n, stage n) = ⊤ := by
    apply top_unique
    rw [← hx]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Submodule.mem_iSup_of_mem i
    exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩
  have stage_fg (n : ℕ) : (N ⊓ stage n).FG := by
    apply Submodule.FG.of_le
      ((Submodule.fg_iff_exists_fin_generating_family).mpr
        ⟨n + 1, fun i => x i.val, rfl⟩)
    exact inf_le_right
  choose length generators span_generators using
    fun n => (Submodule.fg_iff_exists_fin_generating_family).mp (stage_fg n)
  have generators_mem (n : ℕ) (i : Fin (length n)) : generators n i ∈ N := by
    have hi : generators n i ∈ N ⊓ stage n := by
      rw [← span_generators n]
      exact Submodule.subset_span (Set.mem_range_self i)
    exact hi.1
  let family : (Σ n, Fin (length n)) → N := fun p =>
    ⟨generators p.1 p.2, generators_mem p.1 p.2⟩
  have family_span : Submodule.span R (Set.range family) = ⊤ := by
    apply top_unique
    intro a _
    have ha : (a : M) ∈ ⨆ n, stage n := by rw [stage_top]; trivial
    obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed stage
      stage_mono.directed_le).mp ha
    have ha_stage : (a : M) ∈ N ⊓ stage n := ⟨a.property, hn⟩
    rw [← span_generators n] at ha_stage
    have hle : Submodule.span R (Set.range (generators n)) ≤
        (Submodule.span R (Set.range family)).map N.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨family ⟨n, i⟩, Submodule.subset_span (Set.mem_range_self _), rfl⟩
    obtain ⟨b, hb, hba⟩ := hle ha_stage
    have : b = a := Subtype.ext hba
    exact this ▸ hb
  have : Countable (Σ n, Fin (length n)) := inferInstance
  have family_countable : (Set.range family ∪ {0} : Set N).Countable :=
    (Set.countable_range family).union (Set.countable_singleton 0)
  obtain ⟨sequence, hsequence⟩ := family_countable.exists_eq_range
    ⟨0, Or.inr (Set.mem_singleton 0)⟩
  refine ⟨sequence, ?_⟩
  apply top_unique
  rw [← family_span]
  apply Submodule.span_mono
  rw [← hsequence]
  exact Set.subset_union_left

end Module.CountablyGenerated
