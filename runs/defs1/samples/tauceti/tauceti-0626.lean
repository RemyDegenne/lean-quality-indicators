public section

namespace TauCeti

namespace Quiver

namespace AffineE6

/-- The arrow from the outer vertex of the arm indexed by `i` to the inner vertex of that arm. -/
def outerArrow (i : Fin 3) : outer i ⟶ inner i := PLift.up rfl

end AffineE6
end Quiver
end TauCeti
end
