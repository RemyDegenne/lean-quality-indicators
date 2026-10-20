set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option autoImplicit false

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option maxHeartbeats 400000

set_option synthInstance.maxHeartbeats 400000

set_option maxRecDepth 4000

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero Module IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def poleMulUniformizerPow (n : ℕ) : v.poleSubmodule n →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer ^ n * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer ^ n * ((c • f : v.poleSubmodule n) : F)
        = ((c • ⟨v.uniformizer ^ n * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]

end Place
end AlgebraicCurve
end
