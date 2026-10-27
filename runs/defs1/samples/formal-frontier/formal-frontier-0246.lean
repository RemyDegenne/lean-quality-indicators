@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

/-- The diagram of finite `p`-group quotients of a profinite group. -/
def finiteGrpDiagram : Quotient p G ⥤ FiniteGrp.{u} where
  obj U := ↧(G ⧸ U.toOpenNormalSubgroup.toSubgroup)
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _
    (MonoidHom.id G) f.le
  map_id U := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

end MaximalProPQuotient
end ProfiniteGrp
end
