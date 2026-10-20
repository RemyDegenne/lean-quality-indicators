@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory.IsMonHom.Normal

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [Normal i]

variable {i}

/-- A map from the pointwise quotient presheaf to a group-valued fppf sheaf
extends canonically across quotient sheafification. -/
noncomputable def relativeFppfQuotientSheafifyLift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : yonedaQuotient i ⋙ GrpCat.uliftFunctor.{u + 1, u} ⟶ F.obj) :
    relativeFppfQuotient i ⟶ F :=
  ⟨sheafifyLift (relativeFppfTopology S) f F.property⟩

end CategoryTheory.IsMonHom.Normal
end
end
