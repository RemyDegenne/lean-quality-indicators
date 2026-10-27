public section

namespace CFSG.ClassicalInvolution.ModelFacts.UnitaryAut

open Matrix CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.Models

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem unitary_involution_pattern (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {k : ℕ} (hk : 3 ≤ k) {Y : Type} [Group Y] (θ : Su K p f (k + 2) →* Y)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (k + 2))) (σ : Y ≃* Y) (hσ : ∀ y, σ (σ y) = y)
    (hstab : ∀ x, σ (θ x) ∈ θ.range) (k₀ : Su K p f (k + 2))
    (hR : ∀ A : Su K p f 2,
      σ (θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) 2 0 (by omega) A * k₀⁻¹))
    (hT : ∀ t ∈ torus (unitaryInvolution K p f) k,
      σ (θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) =
        θ (k₀ * blockEmb K p f (k + 2) k 2 (by omega) t * k₀⁻¹)) :
    ∃ v : Fin (k + 2) → ZMod 2, v ⟨0, by omega⟩ = 0 ∧ v ⟨1, by omega⟩ = 0 ∧
      (∀ x : Su K p f (k + 2), σ (θ (k₀ * x * k₀⁻¹)) = θ (k₀ * conjSign hK v x * k₀⁻¹)) ∧
      ∀ T : Pair (k + 2),
        (((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ x ∈ (LcU K p f T).map (MulAut.conj k₀).toMonoidHom, σ (θ x) = θ x) ↔
          charOfU v T = 0) := by
  set θ₀ : Su K p f (k + 2) →* Y := θ.comp (MulAut.conj k₀).toMonoidHom with hθ₀
  have hθ₀x : ∀ x, θ₀ x = θ (k₀ * x * k₀⁻¹) := fun x => rfl
  have hker₀ : θ₀.ker ≤ Subgroup.center (Su K p f (k + 2)) := by
    intro x hx
    have h1 : k₀ * x * k₀⁻¹ ∈ Subgroup.center (Su K p f (k + 2)) :=
      hker (MonoidHom.mem_ker.mpr (by rw [← hθ₀x]; exact MonoidHom.mem_ker.mp hx))
    have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 k₀⁻¹
    simpa [mul_assoc] using h2
  have hstab₀ : ∀ x, σ (θ₀ x) ∈ θ₀.range := fun x => by
    obtain ⟨z, hz⟩ := hstab (k₀ * x * k₀⁻¹)
    refine ⟨k₀⁻¹ * z * k₀, ?_⟩
    change θ (k₀ * (k₀⁻¹ * z * k₀) * k₀⁻¹) = σ (θ (k₀ * x * k₀⁻¹))
    rw [← hz]
    congr 1
    group
  obtain ⟨v, hv0, hv1, hv⟩ :=
    involution_pattern_standard hK hp2 hq hk θ₀ hker₀ σ hσ hstab₀ hR hT
  refine ⟨v, hv0, hv1, hv, fun T => ?_⟩
  obtain ⟨h3, h4⟩ := root_pattern hK hp2 hq (by omega) θ₀ hker₀ σ v hv T
  have hmap : ((LcU K p f T).map (MulAut.conj k₀).toMonoidHom).map θ = (LcU K p f T).map θ₀ :=
    Subgroup.map_map _ _ _
  rw [hmap]
  refine ⟨h3, ?_⟩
  rw [← h4]
  constructor
  · intro hfix x hx
    exact hfix _ ⟨x, hx, rfl⟩
  · intro hfix y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hfix x hx

end Main
end CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
end
