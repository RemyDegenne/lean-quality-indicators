public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

namespace GGSixCtxV2

variable (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)

include h

theorem stdType : LargeEvenStandardType p B x L := h.1.2.2.2.2.2.2.2

end GGSixCtxV2
end Ctx
end CFSG.StandardType
end
