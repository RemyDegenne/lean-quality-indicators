public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.ComponentClassification.UnbalancedCatalog CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K] [CharP K 2]

section Family

variable [Finite K]

theorem invAutGen_antiSp_of_torus {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ (2 * m + 1))
    (η : MulAut (antiSp K)) (hη2 : η * η = 1) (hη1 : η ≠ 1)
    (hT : ∀ t₁ t₂ : Kˣ, η (torElt t₁ t₂) ∈ antiTorus K) (hJ : η jElt = jElt)
    (hz : ∀ c : K, η (zElt m c) = zElt m c) : InvAutGen (antiSp K) η := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hq : 2 ^ 2 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ Nat.card K := by rw [hK]; simpa using hq
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_antiSp h4
  obtain ⟨x₀, hx0, hx1⟩ := exists_ne_zero_ne_one (K := K) (by omega)
  have hx : (1 : K) + x₀ ≠ 0 := fun h => hx1 (by
    have : x₀ = -1 := by linear_combination h
    rw [this]
    exact CharTwo.neg_eq 1)
  let U : fixSubgroup η → Subgroup (antiSp K) := fun c =>
    (antiTorus K).map (MulAut.conj (c : antiSp K)).toMonoidHom
  refine invAutGen_of_odd_iSup hsimple hnonab hη2 hη1 (U := U) (fun c => ?_) (fun c x hx => ?_) ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj (c : antiSp K)).injective]
    exact odd_natCard_antiTorus hK (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩)
      Nat.one_le_two_pow
  · obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨⟨t₁, t₂⟩, rfl⟩ := ht
    refine Subgroup.mem_map.mpr ⟨η (torElt t₁ t₂), hT t₁ t₂, ?_⟩
    have hc : η (c : antiSp K) = c := mem_fixSubgroup_iff.mp c.2
    show (c : antiSp K) * η (torElt t₁ t₂) * (c : antiSp K)⁻¹ =
      η ((c : antiSp K) * torElt t₁ t₂ * (c : antiSp K)⁻¹)
    rw [map_mul, map_mul, map_inv, hc]
  · obtain ⟨H, hH⟩ : ∃ H : Subgroup (antiSp K), H = ⨆ c, U c := ⟨_, rfl⟩
    rw [← hH]
    have hTH : ∀ t ∈ antiTorus K, t ∈ H := fun t ht => hH ▸
      Subgroup.mem_iSup_of_mem (1 : fixSubgroup η) (Subgroup.mem_map.mpr ⟨t, ht, by simp⟩)
    have hC : ∀ c : antiSp K, c ∈ fixSubgroup η → ∀ y ∈ H, c * y * c⁻¹ ∈ H := by
      intro c hc y hy
      rw [hH] at hy ⊢
      refine Subgroup.iSup_induction U (C := fun y => c * y * c⁻¹ ∈ ⨆ c, U c) hy ?_ ?_ ?_
      · intro c' y hy
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_iSup_of_mem (⟨c * c', (fixSubgroup η).mul_mem hc c'.2⟩ :
          fixSubgroup η) (Subgroup.mem_map.mpr ⟨t, ht, ?_⟩)
        show (c * (c' : antiSp K)) * t * (c * (c' : antiSp K))⁻¹ =
          c * ((c' : antiSp K) * t * (c' : antiSp K)⁻¹) * c⁻¹
        group
      · simp
      · intro y y' hy hy'
        have : c * (y * y') * c⁻¹ = (c * y * c⁻¹) * (c * y' * c⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ hy hy'
    have hcomm : ∀ (c₀ : K) (t₁ t₂ : Kˣ),
        (uElt 0 ((1 + t₁ * t₂) * c₀ ^ 2 ^ m) ((1 + t₁ ^ 2) * c₀) 0 : antiSp K) ∈ H := by
      intro c₀ t₁ t₂
      have hz' : (uElt 0 (c₀ ^ 2 ^ m) c₀ 0 : antiSp K) ∈ fixSubgroup η :=
        mem_fixSubgroup_iff.mpr (hz c₀)
      have hh := hTH _ (torElt_mem_antiTorus t₁ t₂)
      rw [← uElt_comm_torElt]
      exact H.mul_mem (hC _ hz' _ hh) (H.inv_mem hh)
    have hXc : ∀ s : K, (uElt 0 0 s 0 : antiSp K) ∈ H := by
      intro s
      let t : Kˣ := Units.mk0 (x₀ ^ 2 ^ (2 * m)) (pow_ne_zero _ hx0)
      have ht2 : (t : K) ^ 2 = x₀ := sq_pow_eq hK x₀
      have key := hcomm (s / (1 + x₀)) t t⁻¹
      have e : (uElt 0 0 s 0 : antiSp K) = uElt 0
          ((1 + (t : K) * ((t⁻¹ : Kˣ) : K)) * (s / (1 + x₀)) ^ 2 ^ m)
          ((1 + (t : K) ^ 2) * (s / (1 + x₀))) 0 := by
        rw [Units.mul_inv, ht2]
        congr 1
        · linear_combination (-((s / (1 + x₀)) ^ 2 ^ m)) * h2
        · field_simp
      rw [e]
      exact key
    have hXb : ∀ s : K, (uElt 0 s 0 0 : antiSp K) ∈ H := by
      intro s
      let t : Kˣ := Units.mk0 x₀ hx0
      have ht2 : (t : K) = x₀ := rfl
      have key := hcomm ((s / (1 + x₀)) ^ 2 ^ (m + 1)) 1 t
      have e : (uElt 0 s 0 0 : antiSp K) = uElt 0
          ((1 + ((1 : Kˣ) : K) * (t : K)) * ((s / (1 + x₀)) ^ 2 ^ (m + 1)) ^ 2 ^ m)
          ((1 + ((1 : Kˣ) : K) ^ 2) * (s / (1 + x₀)) ^ 2 ^ (m + 1)) 0 := by
        rw [pow_pow_eq hK, Units.val_one, ht2]
        congr 1
        · field_simp
        · linear_combination (-((s / (1 + x₀)) ^ 2 ^ (m + 1))) * h2
      rw [e]
      exact key
    have hJC : (jElt : antiSp K) ∈ fixSubgroup η := mem_fixSubgroup_iff.mpr hJ
    have hJH : ∀ y ∈ H, jElt * y * jElt⁻¹ ∈ H := hC jElt hJC
    have hJJ : ∀ y : antiSp K, jElt * (jElt * y * jElt⁻¹) * jElt⁻¹ = y := fun y => by
      rw [jElt_inv]
      calc (jElt : antiSp K) * (jElt * y * jElt) * jElt
          = (jElt * jElt) * y * (jElt * jElt) := by group
        _ = y := by rw [jElt_mul_self]; simp
    have hnb : (nb : antiSp K) ∈ H := H.mul_mem (H.mul_mem (hXb 1) (hJH _ (hXb 1))) (hXb 1)
    have hnc : (nc : antiSp K) ∈ H := H.mul_mem (H.mul_mem (hXc 1) (hJH _ (hXc 1))) (hXc 1)
    have hXd : ∀ s : K, (uElt 0 0 0 s : antiSp K) ∈ H := by
      intro s
      have h1 : (jElt * uElt 0 0 0 s * jElt⁻¹ : antiSp K) ∈ H := by
        have e : (jElt * uElt 0 0 0 s * jElt⁻¹ : antiSp K) = nb * uElt 0 0 s 0 * nb⁻¹ := by
          rw [nb_mul_uElt]
          group
        rw [e]
        exact H.mul_mem (H.mul_mem hnb (hXc s)) (H.inv_mem hnb)
      have := hJH _ h1
      rwa [hJJ] at this
    have hXa : ∀ s : K, (uElt s 0 0 0 : antiSp K) ∈ H := by
      intro s
      have h1 : (jElt * uElt s 0 0 0 * jElt⁻¹ : antiSp K) ∈ H := by
        have e : (jElt * uElt s 0 0 0 * jElt⁻¹ : antiSp K) = nc * uElt 0 s 0 0 * nc⁻¹ := by
          rw [nc_mul_uElt]
          group
        rw [e]
        exact H.mul_mem (H.mul_mem hnc (hXb s)) (H.inv_mem hnc)
      have := hJH _ h1
      rwa [hJJ] at this
    have hU : ∀ a b c d : K, (uElt a b c d : antiSp K) ∈ H := fun a b c d => by
      rw [uElt_eq_mul]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hXa a) (hXb _)) (hXc _)) (hXd d)
    exact eq_top_of_uElt_le H hU fun a b c d => hJH _ (hU a b c d)

end Family
end CFSG.Quasithin.F7Two
end
