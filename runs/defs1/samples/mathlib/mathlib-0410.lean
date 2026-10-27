@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F₁₂.obj X₁).PreservesZeroMorphisms]
  [G.Additive] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ (X₂ : C₂), (G₂₃.obj X₂).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*} [DecidableEq ι₄]
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (K₃ : HomologicalComplex C₃ c₃)
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [HasMapBifunctor K₁ K₂ F₁₂ c₁₂] [HasMapBifunctor K₂ K₃ G₂₃ c₂₃]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]

namespace mapBifunctor₁₂

variable [DecidableEq ι₁₂] [HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]

variable (F₁₂ G)

/-- The third differential on a summand
of `mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄`. -/
noncomputable def d₃ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶
      (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).X j :=
  (ComplexShape.ε₂ c₁₂ c₃ c₄ (c₁.π c₂ c₁₂ (i₁, i₂), i₃)) •
    (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).map (K₃.d i₃ (c₃.next i₃)) ≫
      ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ _ j

end mapBifunctor₁₂
end HomologicalComplex
end
