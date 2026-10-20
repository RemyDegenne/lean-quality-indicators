@[expose] public section

open Topology

namespace ContinuousLinearMapWOT

@[inherit_doc]
notation:25 E " →SWOT[" σ "] " F => ContinuousLinearMapWOT σ E F

@[inherit_doc]
notation:25 E " →WOT[" 𝕜 "] " F => ContinuousLinearMapWOT (RingHom.id 𝕜) E F

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂}
  {E F : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

local notation X "⋆" => StrongDual 𝕜₂ X

section Seminorms

variable [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

variable (σ E F) in
/-- The family of seminorms that induce the weak operator topology, namely `‖y (A x)‖` for
all `x` and `y`. -/
def seminormFamily : SeminormFamily 𝕜₂ (E →SWOT[σ] F) (E × F⋆) :=
  fun ⟨x, y⟩ => seminorm x y

end Seminorms
end ContinuousLinearMapWOT
end
