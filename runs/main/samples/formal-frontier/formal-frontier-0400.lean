@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

theorem extendAlgebraicOver_unique (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K))
    (φ : D.toFunctor ⟶ (algebraicOverPoints K).obj Y) (f : X ⟶ Y)
    (hf : D.ι ≫ (algebraicOverPoints K).map f = φ) :
    f = extendAlgebraicOver K X Y D hD φ := by
  apply (algebraicOverOneCoverEquiv K X Y D hD).injective
  rw [algebraicOverOneCoverEquiv_apply, hf]
  exact ((algebraicOverOneCoverEquiv K X Y D hD).apply_symm_apply φ).symm

end AlgebraicGeometry
end
