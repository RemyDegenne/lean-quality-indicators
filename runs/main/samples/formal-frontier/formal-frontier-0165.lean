@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}

lemma existsUnique_oneCover_glue
    {W : MorphismProperty C} [W.HasPullbacks] [W.IsStableUnderBaseChange]
    {D : Subfunctor F} (hD : D.IsOneCoverDense W) {Y : Cᵒᵖ ⥤ Type w}
    (hY : ∀ {X U : C} (f : U ⟶ X), W f →
      Presieve.IsSheafFor Y (Presieve.singleton f))
    (φ : D.toFunctor ⟶ Y) (X : C) (x : F.obj (op X)) :
    ∃! t : Y.obj (op X), ∀ {U : C} (f : U ⟶ X)
      (hx : F.map f.op x ∈ D.obj (op U)),
        Y.map f.op t = φ.app (op U) ⟨F.map f.op x, hx⟩ := by
  obtain ⟨U, f, hf, hx⟩ := hD X x
  obtain ⟨t, ht⟩ := ((Presieve.isSheafFor_singleton (P := Y)).mp (hY f hf)
    (φ.app (op U) ⟨F.map f.op x, hx⟩) (compatible_of_section φ f x hx)).exists
  refine ⟨t, ?_, ?_⟩
  · intro V g hg
    have : HasPullback f g := W.hasPullback g hf
    have hq : W (pullback.snd f g) := W.pullback_snd f g hf
    apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY _ hq).isSeparatedFor
    have hsub : D.toFunctor.map (pullback.fst f g).op ⟨F.map f.op x, hx⟩ =
        D.toFunctor.map (pullback.snd f g).op ⟨F.map g.op x, hg⟩ := by
      apply Subtype.ext
      change F.map (pullback.fst f g).op (F.map f.op x) =
        F.map (pullback.snd f g).op (F.map g.op x)
      calc
        _ = F.map ((pullback.fst f g) ≫ f).op x := by rw [op_comp, F.map_comp]; rfl
        _ = F.map ((pullback.snd f g) ≫ g).op x := by rw [pullback.condition]
        _ = F.map (pullback.snd f g).op (F.map g.op x) := by
          rw [op_comp, F.map_comp]; rfl
    calc
      Y.map (pullback.snd f g).op (Y.map g.op t) =
          Y.map (pullback.fst f g).op (Y.map f.op t) := by
        rw [← comp_apply, ← Y.map_comp, ← op_comp, ← pullback.condition,
          op_comp, Y.map_comp, comp_apply]
      _ = Y.map (pullback.fst f g).op (φ.app (op U) ⟨F.map f.op x, hx⟩) := by
        rw [ht]
      _ = φ.app (op (pullback f g))
          (D.toFunctor.map (pullback.fst f g).op ⟨F.map f.op x, hx⟩) := by
        rw [NatTrans.naturality_apply]
      _ = φ.app (op (pullback f g))
          (D.toFunctor.map (pullback.snd f g).op ⟨F.map g.op x, hg⟩) := by
        rw [hsub]
      _ = Y.map (pullback.snd f g).op (φ.app (op V) ⟨F.map g.op x, hg⟩) := by
        rw [NatTrans.naturality_apply]
  · intro t' ht'
    apply (Presieve.isSeparatedFor_singleton (P := Y)).mp (hY f hf).isSeparatedFor
    exact (ht' f hx).trans ht.symm

end CategoryTheory.Subfunctor
end
