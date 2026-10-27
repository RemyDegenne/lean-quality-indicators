@[expose] public section

set_option warningAsError true

namespace ProfiniteGrp.CompatibleSubgroups

variable (G : ProfiniteGrp)

/-- The subgroup of elements satisfying every quotient condition in a family. -/
def reconstruct (S : Family G) : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (S U).comap (QuotientGroup.mk' U.toSubgroup)

end ProfiniteGrp.CompatibleSubgroups
end
