@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

/-- The factorization through the finite quotient by an open kernel. -/
def kernelFiniteQuotientMap {G : ProfiniteGrp.{u}} {F : Type v} [Group F]
    [TopologicalSpace F] [DiscreteTopology F] (q : G →ₜ* F) :
    G ⧸ (kernelOpenNormal q).toSubgroup →* F :=
  QuotientGroup.kerLift q.toMonoidHom

end ProfiniteGrp.FiniteQuotientHom
end
