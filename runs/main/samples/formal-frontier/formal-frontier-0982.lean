public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

@[reassoc]
lemma Scheme.identityComponentMul_comp_ι (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    Scheme.identityComponentMul G ≫ Scheme.identityComponentι G =
      (Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G] := by
  ext
  exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry
end
