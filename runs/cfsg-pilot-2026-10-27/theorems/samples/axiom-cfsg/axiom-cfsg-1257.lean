public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix

set_option maxRecDepth 100000 in
theorem invQM_facts : ∀ c : Fin 8 → ZMod 2, invQM c * invQM (invQInv c) = 1 := by
  decide +kernel

end CFSG.GroupTheory.GL52
end
