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

/-- The morphism from the relative fppf quotient sheaf by a kernel subgroup
scheme to the sheaf represented by a supplied target. The pointwise map uses
`CategoryTheory.IsMonHom.Normal.yonedaQuotientMap`. -/
noncomputable def relativeFppfQuotientMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    relativeFppfQuotient i ⟶ relativeFppfYoneda Q :=
  relativeFppfQuotientSheafifyLift
    (relativeFppfQuotientPresheafMap q h)

end CategoryTheory.IsMonHom.Normal
end
end
