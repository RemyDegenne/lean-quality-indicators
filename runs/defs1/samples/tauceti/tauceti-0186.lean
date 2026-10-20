public section

namespace TauCeti

namespace Quiver

namespace AffineD

variable {m : ℕ}

/-- The arrow from the spine vertex indexed by `j` to the next one. -/
def spineArrow (j : Fin m) : spine j.castSucc ⟶ (spine j.succ : AffineD m) := PLift.up rfl

end AffineD
end Quiver
end TauCeti
end
