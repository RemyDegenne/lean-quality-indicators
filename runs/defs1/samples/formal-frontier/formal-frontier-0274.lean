@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory.IsMonHom

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [IsMonHom i]

/-- The canonical projection from the functor of points of `G` to the
relative fppf left-coset sheaf. The pointwise coset projection is surjective
before sheafification; this sheaf morphism is locally surjective and epi,
not asserted surjective on every object's sections. -/
noncomputable def relativeFppfCosetMk :
    relativeFppfYonedaType G ⟶ relativeFppfCoset i :=
  ⟨relativeFppfCosetPresheafMk i ≫
    toSheafify (relativeFppfTopology S) (relativeFppfCosetPresheaf i)⟩

end CategoryTheory.IsMonHom
end
end
