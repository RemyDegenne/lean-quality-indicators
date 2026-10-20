public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

@[reassoc]
lemma Scheme.identityComponentInv_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    Scheme.identityComponentInv G ≫ Scheme.identityComponentι G =
      Scheme.identityComponentι G ≫ ι[G] := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry
end
