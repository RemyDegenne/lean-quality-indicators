set_option autoImplicit false

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option linter.unusedSectionVars false

open LinearMap Submodule

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 1600000

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 800000

set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 800000

set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule

open ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve.KwF4gRRTate

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

end TateResDef
end ModularCurve.KwF4gRRTate
end
end
