@[expose] public section

noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory.IsMonHom.Normal

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]

variable (i : H ⟶ G) [Normal i]

variable {i}

/-- A morphism from the relative functor of points of `G` to any group-valued
relative fppf sheaf that kills `H` descends to the quotient sheaf. This is the
relative-sheaf analogue of Milne's Proposition 5.21: it uses the pointwise
`QuotientGroup.lift` followed by Mathlib's `sheafifyLift`, not the existence of
a represented quotient. Uniqueness follows from `relativeFppfQuotientMk_epi`. -/
noncomputable def relativeFppfQuotientLift
    {F : Sheaf (relativeFppfTopology S) GrpCat.{u + 1}}
    (f : relativeFppfYoneda G ⟶ F)
    (hf : (relativeFppfYonedaMap i).hom ≫ f.hom = NatTrans.trivialGrp) :
    relativeFppfQuotient i ⟶ F :=
  relativeFppfQuotientSheafifyLift
    (relativeFppfQuotientPresheafLift f.hom hf)

end CategoryTheory.IsMonHom.Normal
end
end
