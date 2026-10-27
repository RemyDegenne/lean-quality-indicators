public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- Multiplication restricts to the identity component when its Cartesian
square is connected. -/
noncomputable def Scheme.identityComponentMul (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S]
    [ConnectedSpace ((Scheme.identityComponentOver G ⊗
      Scheme.identityComponentOver G).left)] :
    Scheme.identityComponentOver G ⊗ Scheme.identityComponentOver G ⟶
      Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι
    (((Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G]).left)
    (Scheme.range_mul_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        ← Category.assoc, IsOpenImmersion.lift_fac]
      exact ((Scheme.identityComponentι G ⊗ₘ Scheme.identityComponentι G) ≫ μ[G]).w)

end AlgebraicGeometry
end
