@[expose] public section

set_option warningAsError true

namespace ProfiniteGrp.CompatibleSubgroups

variable (G : ProfiniteGrp)

/-- The closed subgroup represented by a family of quotient subgroups. -/
def closedReconstruction (S : Family G) : ClosedSubgroup G where
  toSubgroup := reconstruct G S
  isClosed' := isClosed_reconstruct G S

end ProfiniteGrp.CompatibleSubgroups
end
