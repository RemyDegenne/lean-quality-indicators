@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

theorem isOneCoverDense_range_of_surjective {G : Cᵒᵖ ⥤ Type w}
    (W : MorphismProperty C) [W.ContainsIdentities] (p : G ⟶ F)
    (hp : ∀ X, Function.Surjective (p.app X)) :
    (Subfunctor.range p).IsOneCoverDense W := by
  intro X x
  obtain ⟨y, hy⟩ := hp (op X) x
  refine ⟨X, 𝟙 X, W.id_mem X, ?_⟩
  simp only [op_id, Functor.map_id, Subfunctor.range] at *
  exact ⟨y, hy⟩

end CategoryTheory.Subfunctor
end
