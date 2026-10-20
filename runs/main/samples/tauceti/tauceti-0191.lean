public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u v w

variable {W₁ : Type u} {W₂ : Type v}

variable [AddCommGroup W₁] [Module ℂ W₁]

variable [AddCommGroup W₂] [Module ℂ W₂]

namespace HodgeStructureOn

variable {ω₁ : Conjugation W₁} {ω₂ : Conjugation W₂} {n₁ n₂ : ℤ}

theorem comp_mem_internalHom_piece {W₃ : Type w} [AddCommGroup W₃] [Module ℂ W₃]
    {ω₃ : Conjugation W₃} {n₃ : ℤ} (hs₁ : HodgeStructureOn W₁ ω₁ n₁)
    (hs₂ : HodgeStructureOn W₂ ω₂ n₂) (hs₃ : HodgeStructureOn W₃ ω₃ n₃) {p q : ℤ}
    {f : W₁ →ₗ[ℂ] W₂} {g : W₂ →ₗ[ℂ] W₃} (hf : f ∈ (hs₁.internalHom hs₂).piece p)
    (hg : g ∈ (hs₂.internalHom hs₃).piece q) :
    g ∘ₗ f ∈ (hs₁.internalHom hs₃).piece (p + q) := by
  rw [internalHom_piece, LinearMap.mem_homogeneousSubmodule] at hf hg ⊢
  exact hg.comp hf

end HodgeStructureOn
end TauCeti.Hodge
end
