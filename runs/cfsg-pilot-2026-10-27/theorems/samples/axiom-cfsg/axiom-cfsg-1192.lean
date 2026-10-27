public section

namespace CFSG.RankThree.PartTwo.Sec3

open scoped MatrixGroups IsMulCommutative commutatorElement

open AltSLTwo

section LinearAlgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem three_le_finrank_eigenspace (h2 : (2 : K) ≠ 0) {σ₁ σ₂ τ β₁ β₂ ζ : Module.End K V}
    (h11 : σ₁ * σ₁ = 1) (h22 : σ₂ * σ₂ = 1) (h12 : σ₁ * σ₂ = σ₂ * σ₁)
    (hτ₁ : σ₁ * τ = τ * σ₂) (hτ₂ : σ₂ * τ = τ * (σ₁ * σ₂)) (hτ : Function.Injective τ)
    (hβ₁₁ : β₁ * σ₁ = σ₁ * β₁) (hβ₁₂ : β₁ * σ₂ = σ₂ * β₁) (hβ₂₁ : β₂ * σ₁ = σ₁ * β₂)
    (hβ₂₂ : β₂ * σ₂ = σ₂ * β₂) (hβ₁ : Function.Injective β₁) (hβ₂ : Function.Injective β₂)
    (hζ : β₁ * β₂ = ζ * β₂ * β₁) (hσ₁ : σ₁ ≠ 1) (hdim : Module.finrank K V ≤ 4) :
    3 ≤ Module.finrank K (ζ.eigenspace 1) := by
  have app : ∀ (f g h : Module.End K V), f * g = h → ∀ v, f (g v) = h v := fun f g h e v => by
    rw [← e, Module.End.mul_apply]
  have e11 : ∀ v, σ₁ (σ₁ v) = v := fun v => by rw [app _ _ _ h11, Module.End.one_apply]
  have e22 : ∀ v, σ₂ (σ₂ v) = v := fun v => by rw [app _ _ _ h22, Module.End.one_apply]
  have e12 : ∀ v, σ₁ (σ₂ v) = σ₂ (σ₁ v) := fun v => by rw [app _ _ _ h12, Module.End.mul_apply]
  have eτ₁ : ∀ v, σ₁ (τ v) = τ (σ₂ v) := fun v => by rw [app _ _ _ hτ₁, Module.End.mul_apply]
  have eτ₂ : ∀ v, σ₂ (τ v) = τ (σ₁ (σ₂ v)) := fun v => by
    rw [app _ _ _ hτ₂, Module.End.mul_apply, Module.End.mul_apply]
  have hneg : ∀ (f : Module.End K V) (v : V), f v = v → f v = -v → v = 0 := fun f v h1 h2' => by
    have hv : v = -v := h1.symm.trans h2'
    have h2v : (2 : K) • v = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hv]
      exact add_neg_cancel v
    exact (smul_eq_zero.mp h2v).resolve_left h2
  set W₁ := σ₁.eigenspace 1 ⊓ σ₂.eigenspace (-1) with hW₁
  set W₂ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace 1 with hW₂
  set W₃ := σ₁.eigenspace (-1) ⊓ σ₂.eigenspace (-1) with hW₃
  have mem : ∀ (s t : K) (v : V), v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t ↔
      σ₁ v = s • v ∧ σ₂ v = t • v := fun s t v => by
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  have mem₁ : ∀ v, v ∈ W₁ ↔ σ₁ v = v ∧ σ₂ v = -v := fun v => by
    rw [hW₁, mem, one_smul, neg_one_smul]
  have mem₂ : ∀ v, v ∈ W₂ ↔ σ₁ v = -v ∧ σ₂ v = v := fun v => by
    rw [hW₂, mem, one_smul, neg_one_smul]
  have mem₃ : ∀ v, v ∈ W₃ ↔ σ₁ v = -v ∧ σ₂ v = -v := fun v => by
    rw [hW₃, mem, neg_one_smul]
  have hτ13 : ∀ v ∈ W₁, τ v ∈ W₃ := fun v hv => by
    rw [mem₁] at hv
    rw [mem₃]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, map_neg]⟩
  have hτ32 : ∀ v ∈ W₃, τ v ∈ W₂ := fun v hv => by
    rw [mem₃] at hv
    rw [mem₂]
    exact ⟨by rw [eτ₁, hv.2, map_neg], by rw [eτ₂, hv.2, map_neg, hv.1, neg_neg]⟩
  have hτ21 : ∀ v ∈ W₂, τ v ∈ W₁ := fun v hv => by
    rw [mem₂] at hv
    rw [mem₁]
    exact ⟨by rw [eτ₁, hv.2], by rw [eτ₂, hv.2, hv.1, map_neg]⟩
  have hle : ∀ {W W' : Submodule K V}, (∀ v ∈ W, τ v ∈ W') →
      Module.finrank K W ≤ Module.finrank K W' := fun {W W'} h =>
    LinearMap.finrank_le_finrank_of_injective (f := τ.restrict h)
      (fun x y hxy => Subtype.ext (hτ (congrArg Subtype.val hxy)))
  have hk13 := hle hτ13
  have hk32 := hle hτ32
  have hk21 := hle hτ21
  have hinf₂₃ : W₂ ⊓ W₃ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hneg σ₂ v ((mem₂ v).mp hv.1).2 ((mem₃ v).mp hv.2).2
  have hinf₁ : W₁ ⊓ (W₂ ⊔ W₃) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hsup : W₂ ⊔ W₃ ≤ σ₁.eigenspace (-1) := sup_le inf_le_left inf_le_left
    have h3 := hsup hv.2
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at h3
    exact hneg σ₁ v ((mem₁ v).mp hv.1).1 h3
  have hsum : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) =
      Module.finrank K W₁ + (Module.finrank K W₂ + Module.finrank K W₃) := by
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq W₁ (W₂ ⊔ W₃)
    have e2 := Submodule.finrank_sup_add_finrank_inf_eq W₂ W₃
    rw [hinf₁, finrank_bot, add_zero] at e1
    rw [hinf₂₃, finrank_bot, add_zero] at e2
    rw [e1, e2]
  have hVle : Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) ≤ Module.finrank K V := Submodule.finrank_le _
  obtain ⟨v, hv⟩ : ∃ v, σ₁ v ≠ v := by
    by_contra h
    push Not at h
    exact hσ₁ (LinearMap.ext fun v => by rw [h v, Module.End.one_apply])
  set u := v - σ₁ v with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have hσu : σ₁ u = -u := by rw [hu, map_sub, e11, neg_sub]
  have hup : u + σ₂ u ∈ W₂ := by
    rw [mem₂]
    refine ⟨?_, ?_⟩
    · rw [map_add, e12, hσu, map_neg, neg_add]
    · rw [map_add, e22, add_comm]
  have hum : u - σ₂ u ∈ W₃ := by
    rw [mem₃]
    refine ⟨?_, ?_⟩
    · rw [map_sub, e12, hσu, map_neg]
      abel
    · rw [map_sub, e22, neg_sub]
  have hk1 : 1 ≤ Module.finrank K W₂ ∨ 1 ≤ Module.finrank K W₃ := by
    by_contra hcon
    push Not at hcon
    have h2' : Module.finrank K W₂ = 0 := by omega
    have h3' : Module.finrank K W₃ = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h2' h3'
    have a1 : u + σ₂ u = 0 := by
      have := hup
      rw [h2'] at this
      exact (Submodule.mem_bot K).mp this
    have a2 : u - σ₂ u = 0 := by
      have := hum
      rw [h3'] at this
      exact (Submodule.mem_bot K).mp this
    have h2u : (2 : K) • u = 0 := by
      rw [two_smul]
      calc u + u = (u + σ₂ u) + (u - σ₂ u) := by abel
        _ = 0 := by rw [a1, a2, add_zero]
    exact hu0 ((smul_eq_zero.mp h2u).resolve_left h2)
  have hd₁ : Module.finrank K W₁ = 1 := by omega
  have hd₂ : Module.finrank K W₂ = 1 := by omega
  have hd₃ : Module.finrank K W₃ = 1 := by omega
  have pres : ∀ β : Module.End K V, β * σ₁ = σ₁ * β → β * σ₂ = σ₂ * β → ∀ (s t : K),
      ∀ v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t, β v ∈ σ₁.eigenspace s ⊓ σ₂.eigenspace t := by
    intro β hb1 hb2 s t v hv
    rw [mem] at hv ⊢
    refine ⟨?_, ?_⟩
    · rw [app _ _ _ hb1.symm, Module.End.mul_apply, hv.1, map_smul]
    · rw [app _ _ _ hb2.symm, Module.End.mul_apply, hv.2, map_smul]
  have hfix : ∀ W : Submodule K V, Module.finrank K W = 1 → (∀ v ∈ W, β₁ v ∈ W) →
      (∀ v ∈ W, β₂ v ∈ W) → ∀ v ∈ W, ζ v = v := by
    intro W hW hb1 hb2 v hv
    have hb : ∀ x ∈ W, (β₂ * β₁) x ∈ W := fun x hx => hb2 _ (hb1 x hx)
    have hinj : Function.Injective ((β₂ * β₁).restrict hb) := fun x y hxy => by
      have h' : β₂ (β₁ x) = β₂ (β₁ y) := congrArg Subtype.val hxy
      exact Subtype.ext (hβ₁ (hβ₂ h'))
    obtain ⟨⟨v', hv'⟩, hv'v⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨v, hv⟩
    have hv'v' : β₂ (β₁ v') = v := congrArg Subtype.val hv'v
    have hcomm := apply_apply_comm_of_finrank_eq_one hW hb1 hb2 hv'
    have hζ' : β₁ (β₂ v') = ζ (β₂ (β₁ v')) := by
      change (β₁ * β₂) v' = (ζ * β₂ * β₁) v'
      rw [hζ]
    rw [← hv'v', ← hζ', hcomm]
  have hW₁f := hfix W₁ hd₁ (pres β₁ hβ₁₁ hβ₁₂ 1 (-1)) (pres β₂ hβ₂₁ hβ₂₂ 1 (-1))
  have hW₂f := hfix W₂ hd₂ (pres β₁ hβ₁₁ hβ₁₂ (-1) 1) (pres β₂ hβ₂₁ hβ₂₂ (-1) 1)
  have hW₃f := hfix W₃ hd₃ (pres β₁ hβ₁₁ hβ₁₂ (-1) (-1)) (pres β₂ hβ₂₁ hβ₂₂ (-1) (-1))
  have hsub : W₁ ⊔ (W₂ ⊔ W₃) ≤ ζ.eigenspace 1 := by
    refine sup_le ?_ (sup_le ?_ ?_) <;> intro v hv <;>
      rw [Module.End.mem_eigenspace_iff, one_smul]
    · exact hW₁f v hv
    · exact hW₂f v hv
    · exact hW₃f v hv
  calc 3 = Module.finrank K ↥(W₁ ⊔ (W₂ ⊔ W₃)) := by rw [hsum, hd₁, hd₂, hd₃]
    _ ≤ Module.finrank K (ζ.eigenspace 1) := Submodule.finrank_mono hsub

end LinearAlgebra
end CFSG.RankThree.PartTwo.Sec3
end
