@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

/-- The unique scheme map induced by a transformation from a one-cover dense
subfunctor to represented points. -/
noncomputable def extendAlgebraicOver (X Y : algebraicOver K)
    (D : Subfunctor ((algebraicOverPoints K).obj X))
    (hD : D.IsOneCoverDense (faithfullyFlatTestMorphisms K))
    (φ : D.toFunctor ⟶ (algebraicOverPoints K).obj Y) : X ⟶ Y :=
  (algebraicOverOneCoverEquiv K X Y D hD).symm φ

end AlgebraicGeometry
end
