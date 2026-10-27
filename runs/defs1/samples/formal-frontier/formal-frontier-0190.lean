public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

/-- A basis coordinate as a genuine group-scheme projection onto `Gₐ`. -/
@[expose] def vectorGroupProjection {i : Type u} (b : Module.Basis i K V) (j : i) :
    vectorGroupScheme K V ⟶ additiveGroupScheme K :=
  (hopfSpec (.of K)).map
    (CommHopfAlgCat.ofHom (vectorGroupProjectionBialgHom K V b j)).op

end AlgebraicGeometry
end
end
