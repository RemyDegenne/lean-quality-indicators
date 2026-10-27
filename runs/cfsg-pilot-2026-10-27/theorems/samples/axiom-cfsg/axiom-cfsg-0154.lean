public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.GH74.GLS.Stage2.Local

section Actions

theorem twoNilp_of_two_actions {D B₁ B₂ : Type} [Group D] [Group B₁] [Group B₂] [Finite D]
    [Finite B₁] [Finite B₂] (θ₁ : D →* B₁) (θ₂ : D →* B₂) (A₁ : Subgroup B₁) (A₂ : Subgroup B₂)
    (hA₁ : ∀ d, θ₁ d ∈ A₁) (hA₂ : ∀ d, θ₂ d ∈ A₂) (h₁ : TwoNilp ↥A₁) (h₂ : TwoNilp ↥A₂)
    (hk : IsPGroup 2 ↥(θ₁.ker ⊓ θ₂.ker)) (hkc : θ₁.ker ⊓ θ₂.ker ≤ Subgroup.center D) :
    TwoNilp D := by
  let φ : D →* ↥A₁ × ↥A₂ := (θ₁.codRestrict A₁ hA₁).prod (θ₂.codRestrict A₂ hA₂)
  have hker : φ.ker = θ₁.ker ⊓ θ₂.ker := by
    ext d
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_inf, Prod.ext_iff, Subtype.ext_iff]
  rw [← hker] at hk hkc
  exact twoNilp_of_central_two_ker φ hk hkc (twoNilp_prod h₁ h₂)

end Actions
end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
end
