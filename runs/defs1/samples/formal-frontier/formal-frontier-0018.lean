public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The unit section factors through the identity component. -/
noncomputable def Scheme.identityComponentOne (G : Over S) [GrpObj G]
    [LocallyConnectedSpace G.left] [Nonempty S] [Subsingleton S] :
    𝟙_ (Over S) ⟶ Scheme.identityComponentOver G :=
  Over.homMk (IsOpenImmersion.lift (Scheme.identityComponent G).ι η[G].left
    (Scheme.range_unit_subset_identityComponent G)) (by
      rw [show (Scheme.identityComponentOver G).hom =
        (Scheme.identityComponent G).ι ≫ G.hom from rfl,
        IsOpenImmersion.lift_fac_assoc]
      exact η[G].w)

end AlgebraicGeometry
end
