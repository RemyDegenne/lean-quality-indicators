@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable (C : Type u) [Category.{v} C] [HasShift C ℤ]

variable {C}

variable {T₁ T₂ T₃ : Triangle C}

/-- Make an isomorphism between triangles from the required data. -/
@[simps]
def Triangle.isoMk (A B : Triangle C)
    (iso₁ : A.obj₁ ≅ B.obj₁) (iso₂ : A.obj₂ ≅ B.obj₂) (iso₃ : A.obj₃ ≅ B.obj₃)
    (comm₁ : A.mor₁ ≫ iso₂.hom = iso₁.hom ≫ B.mor₁ := by cat_disch)
    (comm₂ : A.mor₂ ≫ iso₃.hom = iso₂.hom ≫ B.mor₂ := by cat_disch)
    (comm₃ : A.mor₃ ≫ iso₁.hom⟦1⟧' = iso₃.hom ≫ B.mor₃ := by cat_disch) : A ≅ B where
  hom := Triangle.homMk _ _ iso₁.hom iso₂.hom iso₃.hom comm₁ comm₂ comm₃
  inv := Triangle.homMk _ _ iso₁.inv iso₂.inv iso₃.inv
    (by simp only [← cancel_mono iso₂.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₁, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono iso₃.hom, assoc, Iso.inv_hom_id, comp_id,
      comm₂, Iso.inv_hom_id_assoc])
    (by simp only [← cancel_mono (iso₁.hom⟦(1 : ℤ)⟧'), Category.assoc, comm₃,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      Functor.map_id, Category.comp_id])

end CategoryTheory.Pretriangulated
end
end
