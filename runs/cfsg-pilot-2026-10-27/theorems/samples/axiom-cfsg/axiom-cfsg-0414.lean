public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg Matrix

open scoped MatrixGroups

section Cocycle

variable {τ : Tag} {θ δ : Fin τ.rank → ℤ} {J : Set (Fin τ.rank)} {k : Type} [Field k]

theorem cocycle_conj_pinnedX_of_comm (hk : ringChar k ≠ 2)
    (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) {u m d n : ModGL τ k}
    (hud : d * u = u * d) (hm : m ∈ parabolicLevi τ k J) (hn : n ∈ parabolicLevi τ k J)
    (hcoc : u = m * rootSL2 τ k θ WSL)
    (hνd : d * (n * rootSL2 τ k θ WSL) = (n * rootSL2 τ k θ WSL) * d)
    (hμ₀ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k θ c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k (-θ) (μ * c))
    (hμ₁ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k (-θ) c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k θ (μ * c))
    (hμ₂ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k δ c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k (-δ) (μ * c))
    (hμ₃ : ∃ μ : kˣ, ∀ c : k, (n * rootSL2 τ k θ WSL) * pinnedX τ k (-δ) c *
      (n * rootSL2 τ k θ WSL)⁻¹ = pinnedX τ k δ (μ * c))
    (hdiag : ∀ s ∈ parabolicLevi τ k J, d * s = s * d →
      s ∈ diagActSubgroup τ k {θ, -θ, δ, -δ}) :
    ∃ Λ₀ Λ₁ Λ₂ Λ₃ : k, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : k, u * pinnedX τ k θ x * u⁻¹ = pinnedX τ k (-θ) (Λ₀ * x)) ∧
      (∀ x : k, u * pinnedX τ k (-θ) x * u⁻¹ = pinnedX τ k θ (Λ₁ * x)) ∧
      (∀ x : k, u * pinnedX τ k δ x * u⁻¹ = pinnedX τ k (-δ) (Λ₂ * x)) ∧
      (∀ x : k, u * pinnedX τ k (-δ) x * u⁻¹ = pinnedX τ k δ (Λ₃ * x)) := by
  set ν := n * rootSL2 τ k θ WSL with hν
  have hdν : d * ν⁻¹ = ν⁻¹ * d :=
    calc d * ν⁻¹ = ν⁻¹ * (ν * d) * ν⁻¹ := by group
      _ = ν⁻¹ * (d * ν) * ν⁻¹ := by rw [hνd]
      _ = ν⁻¹ * d := by group
  set s₀ := u * ν⁻¹ with hs₀
  have hs₀m : s₀ = m * n⁻¹ := by
    rw [hs₀, hcoc, hν]
    group
  have hs₀J : s₀ ∈ parabolicLevi τ k J := by
    rw [hs₀m]
    exact mul_mem hm (inv_mem hn)
  have hs₀d : d * s₀ = s₀ * d :=
    calc d * (u * ν⁻¹) = (d * u) * ν⁻¹ := by group
      _ = (u * d) * ν⁻¹ := by rw [hud]
      _ = u * (d * ν⁻¹) := by group
      _ = u * (ν⁻¹ * d) := by rw [hdν]
      _ = (u * ν⁻¹) * d := by group
  obtain ⟨a₀, ha₀⟩ := hdiag s₀ hs₀J hs₀d
  have hsν : u = s₀ * ν := by rw [hs₀]; group
  have hθ' := IsRoot.neg hθ
  have hδ' := IsRoot.neg hδ
  obtain ⟨μ₀, hμ₀⟩ := hμ₀
  obtain ⟨μ₁, hμ₁⟩ := hμ₁
  obtain ⟨μ₂, hμ₂⟩ := hμ₂
  obtain ⟨μ₃, hμ₃⟩ := hμ₃
  have e1 : (μ₀ : k) * (μ₁ : k) = 1 :=
    scalar_inv_of_conj_swap hk hθ μ₁.ne_zero hμ₀ hμ₁
  have e2 : (μ₂ : k) * (μ₃ : k) = 1 :=
    scalar_inv_of_conj_swap hk hδ μ₃.ne_zero hμ₂ hμ₃
  have act : ∀ {γ γ' : Fin τ.rank → ℤ} {μ : kˣ}, IsRoot τ γ →
      γ' ∈ ({θ, -θ, δ, -δ} : Set (Fin τ.rank → ℤ)) → IsRoot τ γ' →
      (∀ x : k, ν * pinnedX τ k γ x * ν⁻¹ = pinnedX τ k γ' (μ * x)) →
        ∀ x : k, u * pinnedX τ k γ x * u⁻¹ =
          pinnedX τ k γ' ((rootChar a₀ γ' : k) * (μ * x)) := by
    intro γ γ' μ _ hγ' hr' h x
    calc u * pinnedX τ k γ x * u⁻¹ =
        s₀ * (ν * pinnedX τ k γ x * ν⁻¹) * s₀⁻¹ := by rw [hsν]; group
      _ = _ := by rw [h x, ha₀ γ' hγ' hr']
  refine ⟨(rootChar a₀ (-θ) : k) * μ₀, (rootChar a₀ θ : k) * μ₁,
    (rootChar a₀ (-δ) : k) * μ₂, (rootChar a₀ δ : k) * μ₃, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := rootChar_neg' a₀ θ
    calc (rootChar a₀ (-θ) : k) * μ₀ * ((rootChar a₀ θ : k) * μ₁) =
        ((rootChar a₀ (-θ) * rootChar a₀ θ : kˣ) : k) * (μ₀ * μ₁) := by
          push_cast; ring
      _ = 1 := by rw [this, inv_mul_cancel, Units.val_one, e1, one_mul]
  · have := rootChar_neg' a₀ δ
    calc (rootChar a₀ (-δ) : k) * μ₂ * ((rootChar a₀ δ : k) * μ₃) =
        ((rootChar a₀ (-δ) * rootChar a₀ δ : kˣ) : k) * (μ₂ * μ₃) := by
          push_cast; ring
      _ = 1 := by rw [this, inv_mul_cancel, Units.val_one, e2, one_mul]
  · intro x
    rw [act hθ (Or.inr (Or.inl rfl)) hθ' hμ₀ x, mul_assoc]
  · intro x
    rw [act hθ' (Or.inl rfl) hθ hμ₁ x, mul_assoc]
  · intro x
    rw [act hδ (Or.inr (Or.inr (Or.inr rfl))) hδ' hμ₂ x, mul_assoc]
  · intro x
    rw [act hδ' (Or.inr (Or.inr (Or.inl rfl))) hδ hμ₃ x, mul_assoc]

end Cocycle
end CFSG.ClassicalInvolution.ModelFacts.Levi
end
