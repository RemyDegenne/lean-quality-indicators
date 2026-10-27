public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57

open scoped commutatorElement Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem t₁_inv_conj_Z {z : G} (hz : z ∈ quasithinOmegaOneCenter T) : t₁⁻¹ * z * t₁ = z := by
  have h := t₁_comm_Z S hz
  calc t₁⁻¹ * z * t₁ = t₁⁻¹ * (z * t₁) := by rw [mul_assoc]
    _ = t₁⁻¹ * (t₁ * z) := by rw [h]
    _ = z := by group

end Setting
end S153E56p
end CFSG.Quasithin
end
