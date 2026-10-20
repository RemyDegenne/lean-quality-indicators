@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

variable {G}

variable {P : ProfiniteGrp.{u}} [IsProP p P]

/-- The finite quotient map induced by a homomorphism to a pro-`p` target. -/
def quotientMap (f : G →ₜ* P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸
      (preimage p f H).toOpenNormalSubgroup.toSubgroup) ⟶
      FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.toMonoidHom fun _ h ↦ h

end MaximalProPQuotient
end ProfiniteGrp
end
