@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.IsMonHom.Normal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {H G : C} [GrpObj H] [GrpObj G] (i : H ⟶ G) [Normal i]

/-- The presheaf quotient `X ↦ G(X) / i(H(X))` attached to a normal
morphism of group objects. This construction does not assert that the
presheaf is a sheaf or representable. -/
abbrev yonedaQuotient : Functor Cᵒᵖ GrpCat.{v} :=
  NatTrans.IsPointwiseNormal.quotient
    (yonedaGrp.map (Grp.homMk (A := Grp.mk H) (B := Grp.mk G) i))

end CategoryTheory.IsMonHom.Normal
end
end
