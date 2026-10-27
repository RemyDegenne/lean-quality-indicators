@[expose] public section

namespace ProfiniteGrp

open CategoryTheory

universe u

namespace ProfiniteCompletion

variable (G : GrpCat.{u})

variable {G}

variable {P : ProfiniteGrp.{u}}

/-- The induced map on finite quotients coming from a morphism to `P`. -/
@[to_additive /-- The induced map on finite quotients coming from a morphism to `P`. -/]
def quotientMap (f : G ⟶ ↧P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.hom <| fun _ h => h

end ProfiniteCompletion
end ProfiniteGrp
end
