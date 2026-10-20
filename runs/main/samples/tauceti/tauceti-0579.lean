public section

namespace TauCeti.DynkinType

open Function

@[simp] theorem g2Length_add_six (k : Fin 12) : g2Length (k + 6) = g2Length k := by
  decide +revert

end TauCeti.DynkinType
end
