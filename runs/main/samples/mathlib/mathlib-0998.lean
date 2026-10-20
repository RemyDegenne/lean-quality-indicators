@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] Opposite.small

namespace AlgebraicGeometry

section Coproduct

variable {ι : Type u} (f : ι → Scheme.{u})

variable {σ : Type v} (g : σ → Scheme.{u})

variable (X Y : Scheme.{u})

@[simp]
lemma coprodMk_inl (x : X) :
    coprodMk X Y (.inl x) = (coprod.inl : X ⟶ X ⨿ Y) x := by
  change ((TopCat.binaryCofan X Y).inl ≫
    (colimit.isoColimitCocone ⟨_, TopCat.binaryCofanIsColimit _ _⟩).inv ≫ _) x =
      Scheme.forgetToTop.map coprod.inl x
  congr 2
  refine (colimit.isoColimitCocone_ι_inv_assoc ⟨_, TopCat.binaryCofanIsColimit _ _⟩ _ _).trans ?_
  exact inl_coprodComparison Scheme.forgetToTop _ _

end Coproduct
end AlgebraicGeometry
end
