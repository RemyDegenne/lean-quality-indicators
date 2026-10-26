/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Cofinal

/-!
# Sequentializing directed preorders

This file constructs a monotone cofinal sequence in a nonempty directed
preorder from a countable cofinal subset. In particular, the whole preorder
need not be countable.
-/

@[expose] public section

open CategoryTheory

universe u

namespace IsCofinal

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]

/-- A nonempty directed preorder with a countable cofinal subset admits a
monotone cofinal sequence. -/
theorem exists_monotone_nat {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) :
    ∃ f : ℕ → J, Monotone f ∧ IsCofinal (Set.range f) := by
  let _ : Countable s := hsc.to_subtype
  let _ : Nonempty s := hs.nonempty.to_subtype
  have hsdir : DirectedOn (· ≤ ·) s := by
    intro i hi j hj
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    obtain ⟨l, hls, hkl⟩ := hs k
    exact ⟨l, hls, hik.trans hkl, hjk.trans hkl⟩
  let _ : IsDirectedOrder s := hsdir.isDirectedOrder
  let f : ℕ → J := fun n ↦ CategoryTheory.Limits.IsFiltered.sequentialFunctor_obj s n
  refine ⟨f, ?_, ?_⟩
  · intro m n hmn
    exact CategoryTheory.Limits.IsFiltered.sequentialFunctor_map s hmn
  · intro j
    obtain ⟨k, hks, hjk⟩ := hs j
    obtain ⟨n, hkn⟩ :=
      CategoryTheory.Limits.IsFiltered.sequentialFunctor_final_aux s ⟨k, hks⟩
    exact ⟨f n, ⟨n, rfl⟩, hjk.trans hkn⟩

/-- A nonempty directed preorder with a countable cofinal subset admits a
final functor from `ℕ`. -/
theorem exists_final_functor_nat {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) :
    ∃ F : ℕ ⥤ J, F.Final := by
  obtain ⟨f, hf, hfinal⟩ := hs.exists_monotone_nat hsc
  refine ⟨hf.functor, ?_⟩
  rw [hf.final_functor_iff]
  intro j
  obtain ⟨_, ⟨n, rfl⟩, hj⟩ := hfinal j
  exact ⟨n, hj⟩

end IsCofinal
