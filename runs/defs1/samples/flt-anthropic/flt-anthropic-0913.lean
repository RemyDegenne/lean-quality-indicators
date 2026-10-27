namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace K3cLocMax

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section W

set_option synthInstance.maxHeartbeats 800000

variable {a b : ℚ}

variable (v : HOS) (O : Subring (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
  (hOsmul : ∀ {c : v.adicCompletion ℚ}, c ∈ v.adicCompletionIntegers ℚ →
    ∀ {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ}, x ∈ O → ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ O)

def LambdaPrime (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] where
  carrier := {z | z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ O ∧
    ∀ w : HOS, w ≠ v → z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w}
  zero_mem' := ⟨by rw [TensorProduct.zero_tmul]; exact zero_mem _,
    fun w _ => by rw [TensorProduct.zero_tmul]; exact zero_mem _⟩
  add_mem' := fun {x y} hx hy => ⟨by rw [TensorProduct.add_tmul]; exact add_mem hx.1 hy.1,
    fun w hw => by rw [TensorProduct.add_tmul]; exact add_mem (hx.2 w hw) (hy.2 w hw)⟩
  smul_mem' := fun n x hx => ⟨by rw [← TensorProduct.smul_tmul']; exact zsmul_mem hx.1 n,
    fun w hw => by rw [← TensorProduct.smul_tmul']; exact AddSubgroup.zsmul_mem _ (hx.2 w hw) n⟩

end W
end K3cLocMax
end
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
