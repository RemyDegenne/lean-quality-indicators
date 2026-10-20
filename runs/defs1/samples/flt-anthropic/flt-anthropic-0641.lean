set_option maxHeartbeats 200000

set_option synthInstance.maxHeartbeats 20000

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

abbrev jBar (k : Type) [Field k] : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

end ModularCurve.MultCovering
end
