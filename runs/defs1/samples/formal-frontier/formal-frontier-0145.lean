@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory.IsMonHom.Normal

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [Normal i]

variable {i}

variable {Q : Over S} [GrpObj Q] (q : G ⟶ Q) [IsMonHom q]

/-- The map from the pointwise quotient presheaf by a kernel subgroup scheme
to the lifted relative functor of points of the target. -/
noncomputable def relativeFppfQuotientPresheafMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶
      (relativeFppfYoneda Q).obj :=
  Functor.whiskerRight (yonedaQuotientMap i q h)
    GrpCat.uliftFunctor.{u + 1, u}

end CategoryTheory.IsMonHom.Normal
end
end
