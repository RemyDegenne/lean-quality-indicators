@[expose] public section

namespace Erdos97Octagon

open scoped BigOperators

namespace OctagonIncidence

/-- The number of witness rows containing `a`. -/
def indegree (Q : OctagonIncidence) (a : Vertex) : ℕ :=
  ∑ v, if a ∈ Q.targets v then 1 else 0

end OctagonIncidence
end Erdos97Octagon
end
