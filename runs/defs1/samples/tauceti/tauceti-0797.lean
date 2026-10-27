public section

namespace TauCeti

open _root_.Quiver

namespace Quiver

namespace D4

/-- The length-one path traced by the arrow at an outer vertex. -/
def arrowPath (i : Fin 3) : Path (outer i) center := (arrow i).toPath

end D4
end Quiver
end TauCeti
end
