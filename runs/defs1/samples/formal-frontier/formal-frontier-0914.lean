@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.IsMonHom.Normal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {H G : C} [GrpObj H] [GrpObj G] (i : H ⟶ G) [Normal i]

variable {Q : C} [GrpObj Q] (q : G ⟶ Q) [IsMonHom q]

/-- The map from the pointwise quotient by a kernel subgroup object to the
functor of points of the target group object. -/
noncomputable def yonedaQuotientMap
    (h : IsPullback i (toUnit H) q η[Q]) :
    yonedaQuotient i ⟶ yonedaGrpObj Q := by
  apply NatTrans.IsPointwiseNormal.quotientLift
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))
    (yonedaGrp.map (Grp.homMk (A := Grp.mk G) (B := Grp.mk Q) q))
  intro X
  rw [yonedaGrp_map_app, yonedaMon_map_app, yonedaGrp_map_app, yonedaMon_map_app]
  exact (monoidHom_range_eq_ker_of_isPullback i q h X.unop).le

end CategoryTheory.IsMonHom.Normal
end
end
