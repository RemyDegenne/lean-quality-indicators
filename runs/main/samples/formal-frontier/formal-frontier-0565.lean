@[expose] public section

open CategoryTheory CategoryTheory.IsCofiltered Set

universe u v w

namespace CategoryTheory.Functor

variable {I : Type u} {J : Type v} [Preorder I] [Preorder J]

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

end CategoryTheory.Functor
end
