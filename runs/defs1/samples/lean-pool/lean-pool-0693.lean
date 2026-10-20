@[expose] public section

namespace O3

/-- A point was actually queried in the given trace. -/
def WasQueried (trace : OracleTrace d) (x : Vec d) : Prop :=
  ∃ o ∈ trace, o.point = x

end O3
end
