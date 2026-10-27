public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G]

section Config

variable [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section Core

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hSA : ConstrainedSetupAt)
  (hlin : Lin2BlockExcluded) (ha5 : A5BlockExcluded) (ha3 : SingleA3Excluded)
  (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K)

include hD h27_1 hSA hlin ha5 ha3 h34 hK

theorem A3A3K.mixed_not_mem_conjClass
    (hbot : (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s = ⊥)
    (hcomm : ∀ a ∈ baum S ⊓ K, ∀ b ∈ conjR (baum S ⊓ K) s, a * b = b * a)
    (hR64 : Nat.card (baum S) = 64) {a b : G}
    (ha : a ∈ blockU L ∨ a ∈ conjR (blockU L) x) (hb : b ∈ blockU2 L s) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : a * b ∉ conjClass z₂ := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  obtain ⟨e⟩ := hK.nonempty_alt6 h34
  have hz₁K : z₁ ∈ K := hK.z₁_mem_K
  have hz₁1 : z₁ ≠ 1 := hK.z₁_ne
  have hz₁2 : z₁ * z₁ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₁
  have hcl : ∀ y ∈ K, y * y = 1 → y ≠ 1 → y ∈ conjClass z₂ := fun y hy h2 h1 =>
    involution_mem_conjClass e hz₁K hz₁1 hz₁2 hK.z₂_def hy h2 h1
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hsq : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    simpa [pow_two] using hK.isA4.sq_U u hu
  have hUcl : ∀ p ∈ blockU L, p ≠ 1 → p ∈ conjClass z₂ := fun p hp hp1 =>
    hcl p (hUK hp) (hsq p hp) hp1
  have hne1 : ∀ (g p : G), g * p * g⁻¹ = 1 → p = 1 := fun g p h => by
    have : p = g⁻¹ * (g * p * g⁻¹) * g := by group
    rw [this, h]
    group
  have hUxcl : ∀ p ∈ conjR (blockU L) x, p ≠ 1 → p ∈ conjClass z₂ := fun p hp hp1 =>
    mem_conjClass_of_conj (g := x) (hUcl _ (mem_conjR.mp hp) (fun h => hp1 (hne1 x p h)))
  have hU2cl : ∀ n ∈ blockU2 L s, n ≠ 1 → n ∈ conjClass z₂ := fun n hn hn1 =>
    mem_conjClass_of_conj (g := s) (hUcl _ (mem_conjR.mp hn) (fun h => hn1 (hne1 s n h)))
  have hzT := z_central hB hK.toA3A3x
  have hz₁U : z₁ ∈ blockU L := hK.toA3A3x.z₁_mem.1
  have hz₂U : z₂ ∈ blockU2 L s := hK.toA3A3x.z₂_mem.1
  have hzZ := hK.z_not_mem_conjClass hD h27_1
  have hinf : blockU L ⊓ blockU2 L s = ⊥ := hK.isA4.inf_eq_bot hK.isA4s hK.comm_elem
  rcases ha with haU | haUx
  ·
    have hz : z₁ * z₂ ∈ blockU L ⊔ blockU2 L s := mul_mem (mem_sup_left hz₁U) (mem_sup_right hz₂U)
    have hzU : z₁ * z₂ ∉ blockU L := by
      intro h
      have h2 : z₂ ∈ blockU L := by
        have := mul_mem (inv_mem hz₁U) h
        simpa using this
      have : z₂ ∈ blockU L ⊓ blockU2 L s := ⟨h2, hz₂U⟩
      rw [hinf] at this
      exact hK.toA3A3x.z₂_ne (Subgroup.mem_bot.mp this)
    have hzU₂ : z₁ * z₂ ∉ blockU2 L s := by
      intro h
      have h2 : z₁ ∈ blockU2 L s := by
        have := mul_mem h (inv_mem hz₂U)
        simpa using this
      have : z₁ ∈ blockU L ⊓ blockU2 L s := ⟨hz₁U, h2⟩
      rw [hinf] at this
      exact hz₁1 (Subgroup.mem_bot.mp this)
    have haU' : a ∈ blockU L := haU
    exact no_mixed_mem_conjClass hK.isA4 hK.isA4s hK.comm_elem hz hzU hzU₂ hzZ le_sup_left
      le_sup_right hK.isA4.card_U hK.isA4s.card_U hinf hUcl hU2cl a haU' b hb ha1 hb1
  ·
    obtain ⟨L₁, L₂, U₁, U₂, s', h₁, h₂, hc, hU, hs'T, hU₂⟩ :=
      hK.exists_blocks_A1 hD h27_1 hSA hlin ha5 ha3 hbot hcomm hR64
    have hinf' : U₁ ⊓ U₂ = ⊥ := h₁.inf_eq_bot h₂ hc
    have hz : z₁ * z₂ ∈ U₁ ⊔ U₂ := by rw [hU]; exact hK.z_mem_blockA1
    have hzs : s' * (z₁ * z₂) * s'⁻¹ = z₁ * z₂ := by
      have := Subgroup.mem_centralizer_iff.mp hzT.2 s' hs'T
      rw [this]
      group
    have hz1' : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
    have hzU₁ : z₁ * z₂ ∉ U₁ := by
      intro h
      have h2 : z₁ * z₂ ∈ U₂ := by
        rw [hU₂, mem_conjR, hzs]
        exact h
      have : z₁ * z₂ ∈ U₁ ⊓ U₂ := ⟨h, h2⟩
      rw [hinf'] at this
      exact hz1' (Subgroup.mem_bot.mp this)
    have hzU₂' : z₁ * z₂ ∉ U₂ := by
      intro h
      have h2 : z₁ * z₂ ∈ U₁ := by
        have h3 : s' * (z₁ * z₂) * s'⁻¹ ∈ U₁ := by rw [hU₂] at h; exact mem_conjR.mp h
        rw [hzs] at h3
        exact h3
      have : z₁ * z₂ ∈ U₁ ⊓ U₂ := ⟨h2, h⟩
      rw [hinf'] at this
      exact hz1' (Subgroup.mem_bot.mp this)
    have hUx := hK.blockUx_le_rK hD h27_1
    have hU2R := hK.blockU2_le_rKs
    have hPN : conjR (blockU L) x ⊓ blockU2 L s = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : g ∈ (baum S ⊓ K) ⊓ conjR (baum S ⊓ K) s := ⟨hUx hg.1, hU2R hg.2⟩
      rw [hbot] at this
      exact this
    have hP : conjR (blockU L) x ≤ U₁ ⊔ U₂ := by rw [hU]; exact le_sup_right
    have hN : blockU2 L s ≤ U₁ ⊔ U₂ := by rw [hU]; exact le_sup_left
    exact no_mixed_mem_conjClass h₁ h₂ hc hz hzU₁ hzU₂' hzZ hP hN (hK.isA4.conj x).card_U
      hK.isA4s.card_U hPN hUxcl hU2cl a haUx b hb ha1 hb1

end Core
end Config
end CFSG.QuasithinUnique.DoubleA3
end
