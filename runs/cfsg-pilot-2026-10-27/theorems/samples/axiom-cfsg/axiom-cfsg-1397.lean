public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Inst

variable {G : Type} [Group G] [Finite G]

theorem ivk_3_1b_diag (hII : II4_4_4_center) (h327 : IG_3_27) (h41 : Prop4_1) : IVK_3_1b_diag := by
  intro G _ _ z S K₁ K₂ h q hq hq5 hK₁ hK₂ t₁ ht₁C ht₁o hconj hswap g hg k hk
  have hM := m4_of_std hII h
  have hz2 := h.orderOf_z
  have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁o
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
  have hint₁ : IsIntrinsic t₁ (conjugate K₁ g) := by
    have := isIntrinsic_cj hg (intrinsic_of_comp hM h (Or.inl rfl))
    rwa [cj_eq_conjugate] at this
  have hint₂ : IsIntrinsic t₁ (conjugate K₂ g) := by
    have := isIntrinsic_cj hg (intrinsic_of_comp hM h (Or.inr rfl))
    rwa [cj_eq_conjugate] at this
  have hA₁ := hint₁.1
  have hA₂ := hint₂.1
  have hAne : conjugate K₁ g ≠ conjugate K₂ g := fun he => h.ne (conjugate_inj he)
  have hcs₁ : conjugate K₁ g ≤ cSec (conjugate K₂ g) := le_cSec_of_ne hA₁ hA₂ hAne
  have hcs₂ : conjugate K₂ g ≤ cSec (conjugate K₁ g) := le_cSec_of_ne hA₂ hA₁ hAne.symm
  obtain ⟨hQ, -, hc⟩ := h41 G z S K₁ K₂ h
  have hzint := hc t₁ ht₁C hconj hswap g hg
  have hcz₁ : cmap z (conjugate K₁ g) = conjugate K₂ g := by
    have := hzint.1
    unfold conjugate at this ⊢
    rw [hzi] at this
    exact this
  have hcz₂ : cmap z (conjugate K₂ g) = conjugate K₁ g := by
    have := hzint.2
    unfold conjugate at this ⊢
    rw [hzi] at this
    exact this
  have hKz : cmap z (conjugate K₁ g ⊔ conjugate K₂ g) = conjugate K₁ g ⊔ conjugate K₂ g := by
    show (conjugate K₁ g ⊔ conjugate K₂ g).map (MulAut.conj z).toMonoidHom = _
    rw [Subgroup.map_sup]
    show cmap z (conjugate K₁ g) ⊔ cmap z (conjugate K₂ g) = _
    rw [hcz₁, hcz₂, sup_comm]
  have hK'N₁ : conjugate K₁ g ⊔ conjugate K₂ g ≤ normalizer (conjugate K₁ g : Set G) :=
    sup_le le_normalizer (fun x hx => (hcs₂ hx).1)
  have hoddO := TwoThin.card_pPrimeCoreOf_odd (conjugate K₁ g ⊔ conjugate K₂ g)
  have hD : Diag31 z t₁ (conjugate K₁ g) (conjugate K₂ g)
      (pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g)) :=
    { z_sq := hzsq
      t_sq := ht₁sq
      t_ne := ne_one_of_orderOf_eq_two ht₁o
      tA₁ := hint₁.2.2
      tA₂ := hint₂.2.2
      tcomm := fun x hx =>
        (Subgroup.mem_centralizer_singleton_iff.1 ((sup_le hA₁.1 hA₂.1 : conjugate K₁ g ⊔ conjugate K₂ g ≤
          centralizer ({t₁} : Set G)) hx)).symm
      cz₁ := hcz₁
      cs₁ := hcs₁
      cs₂ := hcs₂
      Oodd := hoddO
      OK := TwoThin.pPrimeCoreOf_le _
      Oz := by
        intro o ho
        have h1 := pPrimeCoreOf_cmap z (conjugate K₁ g ⊔ conjugate K₂ g)
        rw [hKz] at h1
        have h2 : z * o * z⁻¹ ∈ cmap z (pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g)) := by
          rw [mem_cmap]
          have : z⁻¹ * (z * o * z⁻¹) * z = o := by group
          rw [this]; exact ho
        rw [← h1] at h2
        exact h2
      Ocs₁ := by
        intro o ho
        have hoK : o ∈ conjugate K₁ g ⊔ conjugate K₂ g := TwoThin.pPrimeCoreOf_le _ ho
        have hoN : o ∈ normalizer (conjugate K₁ g : Set G) := hK'N₁ hoK
        refine ⟨hoN, TwoThin.mem_normalizer_pPrimeCoreOf hoN, fun k hk => ?_⟩
        have hkK : k ∈ conjugate K₁ g ⊔ conjugate K₂ g := mem_sup_left hk
        have h1 : ⁅k, o⁆ ∈ pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g) := by
          have : ⁅k, o⁆ = (k * o * k⁻¹) * o⁻¹ := rfl
          rw [this]
          exact mul_mem (TwoThin.pPrimeCoreOf_normalized _ hkK ho) (inv_mem ho)
        have h2 : ⁅k, o⁆ ∈ conjugate K₁ g := by
          have : ⁅k, o⁆ = k * (o * k⁻¹ * o⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [this]
          exact mul_mem hk ((Subgroup.mem_normalizer_iff.1 hoN k⁻¹).1 (inv_mem hk))
        have hNle : conjugate K₁ g ⊓ pPrimeCoreOf 2 (conjugate K₁ g ⊔ conjugate K₂ g) ≤
            pPrimeCoreOf 2 (conjugate K₁ g) :=
          le_pPrimeCoreOf' inf_le_left
            (fun x hx n hn => ⟨(conjugate K₁ g).mul_mem ((conjugate K₁ g).mul_mem hx hn.1)
              ((conjugate K₁ g).inv_mem hx), TwoThin.pPrimeCoreOf_normalized _ (mem_sup_left hx) hn.2⟩)
            (Odd.of_dvd_nat hoddO (Subgroup.card_dvd_of_le inf_le_right))
        exact hNle ⟨h2, h1⟩
      Ohat₁ := by
        have hN : ((conjugate K₁ g).subgroupOf (conjugate K₁ g ⊔ conjugate K₂ g)).Normal := by
          rw [sup_comm]
          exact Subgroup.normal_subgroupOf_sup_of_le_normalizer (fun x hx => (hcs₂ hx).1)
        exact pPrimeCoreOf_le_of_normal 2 le_sup_left hN
      Ohat₂ := by
        have hN : ((conjugate K₂ g).subgroupOf (conjugate K₁ g ⊔ conjugate K₂ g)).Normal :=
          Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := conjugate K₁ g) (N := conjugate K₂ g)
            (fun x hx => (hcs₁ hx).1)
        exact pPrimeCoreOf_le_of_normal 2 le_sup_right hN }
  obtain ⟨F₁, _, _, hF₁q, ⟨e₁₀⟩⟩ := hK₁
  obtain ⟨F₂, _, _, hF₂q, ⟨e₂₀⟩⟩ := hK₂
  obtain ⟨c₁⟩ := nonempty_quot_cmap g⁻¹ K₁
  obtain ⟨c₂⟩ := nonempty_quot_cmap g⁻¹ K₂
  let e₁ : Hat (conjugate K₁ g) ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    (c₁.trans e₁₀).trans (specialLinearGroupEquivStatedSL 2 F₁).symm
  let e₂ : Hat (conjugate K₂ g) ≃* Matrix.SpecialLinearGroup (Fin 2) F₂ :=
    (c₂.trans e₂₀).trans (specialLinearGroupEquivStatedSL 2 F₂).symm
  have hodd₁ : Odd (Nat.card F₁) := by rw [hF₁q]; exact hq
  have hcomm : Commute t₁ z := Subgroup.mem_centralizer_singleton_iff.1 ht₁C
  have hzn : z ∉ normalizer (conjugate K₁ g : Set G) := by
    intro hzn
    have h1 : conjugate (conjugate K₁ g) z = conjugate K₁ g := by
      rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 hzn
    exact h.ne (conjugate_inj (h1.symm.trans hzint.1))
  obtain ⟨hI, -⟩ := h327 G h.simple t₁ z ht₁o hz2 hcomm (conjugate K₁ g) hint₁ hzn
  obtain ⟨hIY', hI2⟩ := TwoThin.isPCompIn_two_iff.1 hI
  have hIperf : ⁅IDiag z (conjugate K₁ g), IDiag z (conjugate K₁ g)⁆ = IDiag z (conjugate K₁ g) :=
    TwoThin.commutator_self_of_isTwoComponent hIY' hI2
  have hIne : IDiag z (conjugate K₁ g) ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hI2
  have hIY : IDiag z (conjugate K₁ g) ≤ Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g) := by
    unfold IDiag
    rw [hzint.1]
    exact (pLayerOf_le_self _).trans (le_of_eq (inf_comm _ _))
  have hYY' : Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g) ≤
      centralizer ({t₁} : Set G) ⊓ centralizer ({z} : Set G) := fun x hx =>
    ⟨Subgroup.mem_centralizer_singleton_iff.2 (hD.tcomm x hx.1).symm, hx.2⟩
  have hIsn : ((IDiag z (conjugate K₁ g)).subgroupOf (Diag31.Yz z (conjugate K₁ g) (conjugate K₂ g))).IsSubnormal := by
    obtain ⟨-, -, hsub, -, -⟩ := hI.2
    have := hsub.comap (Subgroup.inclusion hYY')
    convert this using 1
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hcsup : conjugate (K₁ ⊔ K₂) g = conjugate K₁ g ⊔ conjugate K₂ g := Subgroup.map_sup _ _ _
  rw [hcsup] at hk ⊢
  exact hD.main hodd₁ e₁ e₂ hIY hIperf hIne hIsn hk

end Inst
end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
end
