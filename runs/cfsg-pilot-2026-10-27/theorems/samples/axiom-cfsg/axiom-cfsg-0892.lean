public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem typeIII {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (WL : WitnessL2 p) (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} {z : G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hzA : z ∈ A) (hzS : z ∉ Subgroup.normalizer (J₁ : Set G))
    (hV : A ⊓ Subgroup.normalizer (J₁ : Set G) ≠ ⊥) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ M := by
  have hzT : z ∈ T := hAT hzA
  have hz2 : z * z = 1 := by
    have := hAab.2 z hzA
    rwa [pow_two] at this
  have hswap : conjSub z J₁ = J₂ :=
    (h.perm z hzT).resolve_left fun h' => hzS (conjSub_eq_iff_mem_normalizer.mp h')
  have d : TypeIIITwist J₁ J₂ z := ⟨h.comm, h.disj, hz2, hswap⟩
  set D : Subgroup G := typeIII_diag J₁ J₂ z with hDdef
  set R : Subgroup G := T ⊓ Subgroup.centralizer (A : Set G) with hRdef
  set Q : Subgroup G := D ⊔ R with hQdef
  have hRT : R ≤ T := inf_le_left
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp hr.2 z hzA).symm
  have hRN : R ≤ Subgroup.normalizer (D : Set G) := fun r hr =>
    TypeIIITwist.mem_normalizer_diag h.normal_X (hRz r hr)
  have hDQ : D ≤ Q := le_sup_left
  have hRQ : R ≤ Q := le_sup_right
  have hQN : Q ≤ Subgroup.normalizer (D : Set G) := sup_le Subgroup.le_normalizer hRN
  have hDn : (D.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hQN
  have hDp : IsPSL 2 p 1 ↥D := CFSG.SectionRank.statedClassicalModel_of_mulEquiv d.equiv.symm h.psl₁
  have hDs : IsSimpleGroup ↥D := by
    have := h.simple₁
    exact d.equiv.symm.isSimpleGroup
  have hDnc : ∃ a b : ↥D, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.nonab₁
    refine ⟨d.equiv a, d.equiv b, fun hc => hab (d.equiv.injective ?_)⟩
    rw [map_mul, map_mul]
    exact hc
  have hDTQ : D ⊔ (T ⊓ Q) = Q :=
    le_antisymm (sup_le hDQ inf_le_right) (sup_le le_sup_left (le_sup_of_le_right (le_inf hRT hRQ)))
  have hTQ : IsSylowIn 2 (T ⊓ Q) Q := by
    have h1 : IsSylowIn 2 ((T ⊓ Q) ⊓ D) D := by
      have e : (T ⊓ Q) ⊓ D = T ⊓ D := by rw [inf_assoc, inf_eq_right.mpr hDQ]
      rw [e]
      exact typeIII_sylow_diag h d hzT
    have h2 := E1.isSylowIn_two_of_sup_inf (inf_le_right.trans hQN)
      (h.sylow.isPGroup.to_le inf_le_left) h1
    rwa [hDTQ] at h2
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ Q := by
    rw [h.tau_eq A]
    exact le_inf hRT hRQ
  have hAQ : A ≤ Q := fun a ha =>
    hRQ ⟨hAT ha, Subgroup.mem_centralizer_iff.mpr fun b hb => typeIII_comm_of_mem hAab hb ha⟩
  have hAD : ¬ A ≤ Subgroup.centralizer (D : Set G) := by
    obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A ⊓ Subgroup.normalizer (J₁ : Set G), a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hV (eq_bot_iff.mpr fun a ha => Subgroup.mem_bot.mpr (hcon a ha))
    intro hAc
    refine ha1 (d.eq_one_of_centralizes_diag h.cent ha.2 (typeIII_comm_of_mem hAab ha.1 hzA) ?_)
    intro δ hδ
    exact Subgroup.mem_centralizer_iff.mp (hAc ha.1) δ hδ
  have hzD : typeIII_tw z z₁ ∈ D := d.tw_mem_diag h.z₁_mem
  have hzD2 : orderOf (typeIII_tw z z₁) = 2 := by
    have h1 : orderOf (d.hom ⟨z₁, h.z₁_mem⟩) = orderOf (⟨z₁, h.z₁_mem⟩ : ↥J₁) :=
      orderOf_injective d.hom d.hom_injective _
    rw [Subgroup.orderOf_mk, h.z₁_ord] at h1
    exact h1
  have hzc : ∀ x ∈ T ⊓ Q, typeIII_tw z z₁ * x = x * typeIII_tw z z₁ := by
    intro x hx
    obtain ⟨δ, hδ, r, hr, rfl⟩ := typeIII_exists_mul_of_le_normalizer hRN hx.2
    have hδT : δ ∈ T := by
      have := T.mul_mem hx.1 (T.inv_mem hr.1)
      simpa using this
    obtain ⟨x₀, hx₀J, rfl⟩ := d.exists_tw hδ
    have hx₀T : x₀ ∈ T := d.mem_of_tw_mem h.TX_eq.le hx₀J hδT
    have h1 : z₁ * x₀ = x₀ * z₁ := h.z₁_central x₀ ⟨hx₀T, Subgroup.le_normalizer hx₀J⟩
    have hc1 : typeIII_tw z z₁ * typeIII_tw z x₀ = typeIII_tw z x₀ * typeIII_tw z z₁ :=
      d.tw_comm h.z₁_mem hx₀J h1
    have hc2 := typeIII_zD_comm_of_mem h d hzT hr.1 (hRz r hr)
    calc typeIII_tw z z₁ * (typeIII_tw z x₀ * r) = (typeIII_tw z z₁ * typeIII_tw z x₀) * r := by
          group
      _ = (typeIII_tw z x₀ * typeIII_tw z z₁) * r := by rw [hc1]
      _ = typeIII_tw z x₀ * (typeIII_tw z z₁ * r) := by group
      _ = typeIII_tw z x₀ * (r * typeIII_tw z z₁) := by rw [hc2]
      _ = typeIII_tw z x₀ * r * typeIII_tw z z₁ := by group
  obtain ⟨J, hJQ, hJE, hJz⟩ := local_witness WL h.sylow hAT hAab hDQ hDn hDp hDs hDnc hTQ hDTQ hτ
    hAQ hAD hzD hzD2 hzc
  refine ⟨J, hJE, fun hJM => hJz fun g hg => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact typeIII_comm_of_mem_M h d hzT (hJM hg) (hQN (hJQ hg))

end CFSG.Quasithin.E2.E22N
end
