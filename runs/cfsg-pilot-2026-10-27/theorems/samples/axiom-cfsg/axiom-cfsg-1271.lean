public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

section Tensor

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

variable [Finite G] {M : Subgroup G}

theorem inv_mul_mem_Q_of_actsAsTensor (H : StrothHyp M Q Z) {s₁ s₂ : G} (h₁ : s₁ ∈ M)
    (h₂ : s₂ ∈ M) {g g' : Matrix (Fin 2) (Fin 2) K} (hgg : g * g' = 1)
    (hs₁ : ActsAsTensor Q Z M₀ φ s₁ g id) (hs₂ : ActsAsTensor Q Z M₀ φ s₂ g id) :
    s₁⁻¹ * s₂ ∈ Q := by
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hy) x).mp hx
  have hi : ActsAsTensor Q Z M₀ φ s₁⁻¹ g' id :=
    actsAsTensor_id_inv (fun x hx => by simpa using hQM s₁⁻¹ (M.inv_mem h₁) x hx) hs₁ hgg
  have hm := actsAsTensor_id_mul (hQM s₂ h₂) hi hs₂
  rw [mul_eq_one_comm.mp hgg] at hm
  exact mem_Q_of_actsAsTensor_one H (M.mul_mem (M.inv_mem h₁) h₂) hm

end Tensor
end CFSG.RankThree.GF2n.Smith81
end
