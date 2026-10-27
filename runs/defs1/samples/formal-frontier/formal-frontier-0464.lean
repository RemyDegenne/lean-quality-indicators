@[expose] public section

universe v u

namespace CategoryTheory.ShortComplex.SnakeInput

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex.SnakeInput C)

/-- The left endpoint map exhibits the kernel of the first kernel-row arrow. -/
noncomputable def kernelToL₀X₁IsKernel :
    IsLimit (KernelFork.ofι S.kernelToL₀X₁ S.kernelToL₀X₁_comp_f) := by
  haveI : Mono S.kernelToL₀X₁ := mono_of_mono_fac S.kernelToL₀X₁_comp_v₀₁
  apply KernelFork.IsLimit.ofι'
  intro T t ht
  let lift := KernelFork.IsLimit.lift' (kernelIsKernel S.L₁.f)
    (t ≫ S.v₀₁.τ₁) (by
      rw [Category.assoc, S.v₀₁.comm₁₂, ← Category.assoc, ht, zero_comp])
  refine ⟨lift.1, ?_⟩
  apply (cancel_mono S.v₀₁.τ₁).mp
  rw [Category.assoc, S.kernelToL₀X₁_comp_v₀₁]
  exact lift.2

end CategoryTheory.ShortComplex.SnakeInput
end
