@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows

variable (C ι : Type*) [Category* C] [Category* ι] [HasZeroObject C]
  [HasShift C ℤ] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Triangulated

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

section

variable {ι' : Type*} [Category ι'] (F : ι' ⥤ ι)

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] Precomp.map Precomp.obj δ in
/-- The precomposition of a spectral object with a functor. -/
def precomp : SpectralObject C ι' where
  ω₁ := F.mapComposableArrows 1 ⋙ X.ω₁
  δ'.app D := X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom ≫
      X.δ'.app ((F.mapComposableArrows 2).obj D) ≫
      (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)⟦1⟧'
  δ'.naturality D₁ D₂ f := by
    have := X.δ'.naturality ((F.mapComposableArrows 2).map f)
    rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)] at this
    rw [← cancel_mono ((X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).hom)⟦(1 : ℤ)⟧')]
    dsimp at this ⊢
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
      Iso.inv_hom_id, Functor.map_id, Category.comp_id] at this ⊢
    convert this using 3
    · cat_disch
    · congr 2; cat_disch
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    refine isomorphic_distinguished _ (X.triangle_distinguished (F.map f) (F.map g)) _ ?_
    refine Triangle.isoMk _ _ (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _)))
      (X.ω₁.mapIso (ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _))) ?_ ?_ ?_
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · dsimp
      simp only [← Functor.map_comp]
      congr 1
      cat_disch
    · have := X.δ'.naturality (F.mapComposableArrowsObjMk₂Iso f g).hom
      dsimp at this ⊢
      rw [← cancel_epi (X.ω₁.map (F.mapComposableArrowsObjMk₁Iso _).inv)]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
        Iso.inv_hom_id, Functor.map_id, Category.id_comp] at this ⊢
      convert this.symm using 3
      · congr; cat_disch
      · cat_disch

end
end SpectralObject
end Triangulated
end CategoryTheory
end
