@[expose] public section

namespace GoemansFlow

/-- Terminal of commodity `i`. -/
def terminal (i : Fin 3) : Vertex := if i = 0 then .t1 else if i = 1 then .t2 else .t3

end GoemansFlow
end
