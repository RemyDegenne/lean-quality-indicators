@[expose] public section

noncomputable section

open RCLike Real Filter Bornology

open scoped Topology ComplexConjugate

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

export Inner (inner)

scoped[InnerProductSpace] notation:max "⟪" x ", " y "⟫_" 𝕜:max => inner 𝕜 x y

namespace InnerProductSpace.Core

section PreInnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : PreInnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "ext_iff" => @RCLike.ext_iff 𝕜 _

local postfix:90 "†" => starRingEnd _

attribute [local instance] toPreInner'

local notation "normSqF" => @normSq 𝕜 F _ _ _ _

theorem inner_smul_ofReal_left (x y : F) {t : ℝ} : ⟪(t : 𝕜) • x, y⟫ = ⟪x, y⟫ * t := by
  rw [inner_smul_left, conj_ofReal, mul_comm]

end PreInnerProductSpace.Core
end InnerProductSpace.Core
end
end
