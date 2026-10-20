@[expose] public section

open CategoryTheory

universe u

namespace ProfiniteGrp

theorem closedNormalQuotientProj_isQuotientMap (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    Topology.IsQuotientMap (G.closedNormalQuotientProj N hN) :=
  QuotientGroup.isQuotientMap_mk N.toSubgroup

end ProfiniteGrp
end
