/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.CofinalSequence
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.Final.Type
public import Mathlib.CategoryTheory.Limits.Types.Images

/-!
# Mittag--Leffler inverse systems of types

This file develops the countably cofinal form of the nonempty-section theorem
for Mittag--Leffler inverse systems of types. It also identifies the image of
each evaluation map from compatible sections with the eventual range.
-/

@[expose] public section

open CategoryTheory CategoryTheory.IsCofiltered Set

universe u v w

namespace CategoryTheory.Functor

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]

/-- Restriction along a monotone cofinal map preserves the Mittag--Leffler
condition for inverse systems indexed by directed preorders. The source preorder
need not be nonempty. -/
theorem IsMittagLeffler.comp_monotone_cofinal [IsDirectedOrder I]
    (F : Jᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler) {f : I → J} (hf : Monotone f)
    (hfc : IsCofinal (Set.range f)) : (hf.functor.op ⋙ F).IsMittagLeffler := by
  intro i
  obtain ⟨j, g, hg⟩ := hF (Opposite.op (f i.unop))
  obtain ⟨_, ⟨i₀, rfl⟩, hji₀⟩ := hfc j.unop
  obtain ⟨k, hi₀k, hik⟩ := exists_ge_ge i₀ i.unop
  let e : Opposite.op k ⟶ i := (homOfLE hik).op
  refine ⟨Opposite.op k, e, fun l h ↦ ?_⟩
  change Set.range (F.map (hf.functor.op.map e)) ⊆
    Set.range (F.map (hf.functor.op.map h))
  let q : Opposite.op (f k) ⟶ j := (homOfLE (hji₀.trans (hf hi₀k))).op
  have heq : q ≫ g = hf.functor.op.map e := Subsingleton.elim _ _
  have hsub : Set.range (F.map (hf.functor.op.map e)) ⊆ Set.range (F.map g) := by
    rw [← heq, F.map_comp, types_comp]
    exact range_comp_subset_range _ _
  exact hsub.trans (hg (hf.functor.op.map h))

/-- A surjective inverse sequence of nonempty types has a compatible section. -/
theorem nonempty_sections_of_surjective_inverse_sequence (F : ℕᵒᵖ ⥤ Type u)
    [∀ n, Nonempty (F.obj n)]
    (hF : ∀ n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    F.sections.Nonempty := by
  let x₀ : F.obj (Opposite.op 0) := Classical.arbitrary _
  obtain ⟨x, -⟩ := Limits.Types.surjective_π_app_zero_of_surjective_map
    (Limits.limit.isLimit F) hF x₀
  let y : F.sections := Limits.Types.limitEquivSections F x
  exact ⟨y.val, y.property⟩

/-- A pointwise nonempty Mittag--Leffler inverse system of types over a
nonempty directed preorder with a countable cofinal subset has a compatible
section. -/
theorem IsMittagLeffler.nonempty_sections_of_countable_cofinal
    [IsDirectedOrder J] [Nonempty J] (F : Jᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler)
    [∀ j, Nonempty (F.obj j)] {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) :
    F.sections.Nonempty := by
  obtain ⟨f, hf, hfc⟩ := hs.exists_monotone_nat hsc
  let G : ℕᵒᵖ ⥤ Jᵒᵖ := hf.functor.op
  let _ : hf.functor.Final := (hf.final_functor_iff).2 fun j ↦ by
    obtain ⟨_, ⟨n, rfl⟩, hj⟩ := hfc j
    exact ⟨n, hj⟩
  let _ : G.Initial := inferInstance
  have hFG : (G ⋙ F).IsMittagLeffler := hF.comp_monotone_cofinal F hf hfc
  let E : ℕᵒᵖ ⥤ Type w := (G ⋙ F).toEventualRanges
  let _ : ∀ n, Nonempty ((G ⋙ F).obj n) := fun n ↦
    inferInstanceAs (Nonempty (F.obj (G.obj n)))
  let _ : ∀ n, Nonempty (E.obj n) := fun n ↦
    toEventualRanges_nonempty (G ⋙ F) hFG n
  have hE : ∀ n, Function.Surjective (E.map (homOfLE (Nat.le_succ n)).op) :=
    fun n ↦ surjective_toEventualRanges (G ⋙ F) hFG _
  obtain ⟨x, hx⟩ := nonempty_sections_of_surjective_inverse_sequence E hE
  let y : (G ⋙ F).sections := (G ⋙ F).toEventualRangesSectionsEquiv ⟨x, hx⟩
  obtain ⟨z, -⟩ := (G.bijective_sectionsPrecomp F).2 y
  exact ⟨z.val, z.property⟩

/-- Evaluation of a compatible section lands in the eventual range. -/
def evalSectionToEventualRange (F : Jᵒᵖ ⥤ Type w) (i : Jᵒᵖ) :
    F.sections → F.eventualRange i :=
  fun x ↦ ⟨x.val i, F.mem_eventualRange_iff.2 fun _ g ↦ ⟨x.val _, x.property g⟩⟩

/-- For a Mittag--Leffler inverse system indexed by a nonempty directed
preorder with a countable cofinal subset, evaluation maps compatible sections
surjectively onto the eventual ranges. -/
theorem IsMittagLeffler.surjective_evalSectionToEventualRange
    [IsDirectedOrder J] [Nonempty J] (F : Jᵒᵖ ⥤ Type w) (hF : F.IsMittagLeffler)
    {s : Set J} (hs : IsCofinal s) (hsc : s.Countable) (i : Jᵒᵖ) :
    Function.Surjective (F.evalSectionToEventualRange i) := by
  intro x
  let P : Jᵒᵖ ⥤ Type w := F.toPreimages ({x.val} : Set (F.obj i))
  let _ : ∀ j, Nonempty (P.obj j) := fun j ↦ by
    obtain ⟨k, fkj, fki, -⟩ := IsCofilteredOrEmpty.cone_objs j i
    obtain ⟨y, hy⟩ := F.mem_eventualRange_iff.1 x.property fki
    refine ⟨⟨F.map fkj y, ?_⟩⟩
    rw [mem_iInter]
    intro g
    rw [mem_preimage, mem_singleton_iff, ← comp_apply, ← F.map_comp]
    simpa only [hy] using congrArg (fun h ↦ F.map h y) (Subsingleton.elim (fkj ≫ g) fki)
  have hP : P.IsMittagLeffler := hF.toPreimages F ({x.val} : Set (F.obj i))
  obtain ⟨y₀, hy₀⟩ := hP.nonempty_sections_of_countable_cofinal P hs hsc
  let y : P.sections := ⟨y₀, hy₀⟩
  let z : F.sections :=
    ⟨fun j ↦ (y.val j).val, fun g ↦ congrArg Subtype.val (y.property g)⟩
  refine ⟨z, Subtype.ext ?_⟩
  change (y.val i).val = x.val
  have hi := (y.val i).property
  rw [mem_iInter] at hi
  simpa only [mem_preimage, mem_singleton_iff, F.map_id, id_apply] using hi (𝟙 i)

end CategoryTheory.Functor
