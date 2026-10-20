@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

theorem IsOneCoverDense.product {G : Cᵒᵖ ⥤ Type w}
    {W : MorphismProperty C} [W.IsStableUnderComposition]
    {D : Subfunctor F} {E : Subfunctor G}
    (hD : D.IsOneCoverDense W) (hE : E.IsOneCoverDense W) :
    (D.product E).IsOneCoverDense W := by
  intro X x
  obtain ⟨U, f, hf, hx⟩ := hD X ((Limits.prod.fst : F ⨯ G ⟶ F).app (op X) x)
  obtain ⟨V, g, hg, hy⟩ := hE U
    ((Limits.prod.snd : F ⨯ G ⟶ G).app (op U) ((F ⨯ G).map f.op x))
  refine ⟨V, g ≫ f, W.comp_mem g f hg hf, ?_⟩
  rw [mem_product_iff, op_comp, Functor.map_comp]
  constructor
  · change ((Limits.prod.fst : F ⨯ G ⟶ F).app (op V)
        ((F ⨯ G).map g.op ((F ⨯ G).map f.op x))) ∈ D.obj (op V)
    rw [NatTrans.naturality_apply (Limits.prod.fst : F ⨯ G ⟶ F) g.op,
      NatTrans.naturality_apply (Limits.prod.fst : F ⨯ G ⟶ F) f.op]
    exact D.map g.op hx
  · change ((Limits.prod.snd : F ⨯ G ⟶ G).app (op V)
        ((F ⨯ G).map g.op ((F ⨯ G).map f.op x))) ∈ E.obj (op V)
    rwa [NatTrans.naturality_apply (Limits.prod.snd : F ⨯ G ⟶ G) g.op]

end CategoryTheory.Subfunctor
end
