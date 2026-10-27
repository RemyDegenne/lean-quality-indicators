public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isChiefStep_centralizer_of_commutatorMap {H Q Z : Subgroup G} {c : G}
    (hZc : ∀ z ∈ Z, ∀ y ∈ Q, z * y = y * z)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) (hQH : Q ≤ H)
    (hstep : IsChiefStep H Q ⊥ Z) (hnc : ¬ IsCentralStep H ⊥ Z) (hcQ : c ∈ Q)
    (hc : ∀ g ∈ H, g * c * g⁻¹ * c⁻¹ ∈ Z)
    (hsurj : ∀ z ∈ Z, ∃ y ∈ Q, c * y * c⁻¹ * y⁻¹ = z) :
    IsChiefStep H Q (Q ⊓ Subgroup.centralizer ({c} : Set G)) Q ∧
      ¬ IsCentralStep H (Q ⊓ Subgroup.centralizer ({c} : Set G)) Q := by
  have hcZ : ∀ y ∈ Q, c * y * c⁻¹ * y⁻¹ ∈ Z :=
    fun y hy => commutatorMap_mem_of_fixed hc hQH hy
  let φ := commutatorMapHom hZc hcZ
  let K : Subgroup G := Q ⊓ Subgroup.centralizer ({c} : Set G)
  change IsChiefStep H Q K Q ∧ ¬ IsCentralStep H K Q
  have hKQ : K ≤ Q := inf_le_left
  have hKn : IsNormalIn H Q K := isNormalIn_centralizer hZc hHQ hQH hcQ hc
  have hKlt : K < Q := by
    refine lt_of_le_of_ne hKQ ?_
    intro hKQeq
    have hZne : Z ≠ ⊥ := hstep.2.2.1.ne'
    obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨y, hyQ, hφy⟩ := hsurj z hzZ
    have hφy' : φ ⟨y, hyQ⟩ = z := hφy
    have hφne : φ ⟨y, hyQ⟩ ≠ 1 := by
      rw [hφy']
      exact hz1'
    have hyNotK : y ∉ K := by
      intro hyK
      exact hφne ((commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hyQ).mpr hyK.2)
    exact hyNotK (hKQeq.symm ▸ hyQ)
  have hmax : ∀ K' : Subgroup G, IsNormalIn H Q K' → K ≤ K' → K' ≤ Q →
      K' = K ∨ K' = Q := by
    intro K' hK'n hKK' hK'Q
    let J : Subgroup G := (K'.subgroupOf Q).map φ
    have hJleZ : J ≤ Z := by
      intro u hu
      rcases Subgroup.mem_map.mp hu with ⟨y, -, rfl⟩
      exact hcZ (y : G) y.2
    have hJn : IsNormalIn H Q J := by
      refine ⟨hJleZ.trans hstep.1.1, ?_⟩
      intro g hg u hu
      rcases Subgroup.mem_map.mp hu with ⟨y, hy, rfl⟩
      have hyK' : (y : G) ∈ K' := Subgroup.mem_subgroupOf.mp hy
      have hgyQ : g * (y : G) * g⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hHQ hg) (y : G)).mp y.2
      have hgyK' : g * (y : G) * g⁻¹ ∈ K' := hK'n.2 g hg (y : G) hyK'
      refine Subgroup.mem_map.mpr
        ⟨⟨g * (y : G) * g⁻¹, hgyQ⟩, Subgroup.mem_subgroupOf.mpr hgyK', ?_⟩
      exact commutatorMap_conj hZc hHQ hcQ hc hg y.2
    rcases hstep.2.2.2 J hJn bot_le hJleZ with hJbot | hJZ
    · left
      refine le_antisymm ?_ hKK'
      intro x hxK'
      have hxQ : x ∈ Q := hK'Q hxK'
      have hxJ : φ ⟨x, hxQ⟩ ∈ J :=
        Subgroup.mem_map.mpr
          ⟨⟨x, hxQ⟩, Subgroup.mem_subgroupOf.mpr hxK', rfl⟩
      rw [hJbot, Subgroup.mem_bot] at hxJ
      exact ⟨hxQ, (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hxQ).mp hxJ⟩
    · right
      refine le_antisymm hK'Q ?_
      intro x hxQ
      have hxJ : φ ⟨x, hxQ⟩ ∈ J := by
        rw [hJZ]
        exact hcZ x hxQ
      rcases Subgroup.mem_map.mp hxJ with ⟨k', hk'mem, hk'eq⟩
      have hk'K' : (k' : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk'mem
      have hk'Q : (k' : G) ∈ Q := k'.2
      have hkK : (k' : G)⁻¹ * x ∈ K := by
        have hxinvQ : (k' : G)⁻¹ * x ∈ Q := Q.mul_mem (Q.inv_mem hk'Q) hxQ
        refine ⟨hxinvQ, ?_⟩
        have hφ1 : φ ⟨(k' : G)⁻¹ * x, hxinvQ⟩ = 1 := by
          have hsub : (⟨(k' : G)⁻¹ * x, hxinvQ⟩ : ↥Q) =
              (⟨k', hk'Q⟩ : ↥Q)⁻¹ * ⟨x, hxQ⟩ := rfl
          rw [hsub, map_mul, map_inv, hk'eq]
          group
        exact (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ hxinvQ).mp hφ1
      have hxK' : (k' : G) * ((k' : G)⁻¹ * x) ∈ K' :=
        K'.mul_mem hk'K' (hKK' hkK)
      simpa [mul_assoc] using hxK'
  refine ⟨⟨?_, hKn, hKlt, hmax⟩, ?_⟩
  ·
    refine ⟨le_refl Q, ?_⟩
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.mp (hHQ hg) x).mp hx
  ·
    intro hcent
    apply hnc
    intro g hg z hz
    obtain ⟨y, hyQ, hφy⟩ := hsurj z hz
    have hφy' : φ ⟨y, hyQ⟩ = z := hφy
    have hgyQ : g * y * g⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hHQ hg) y).mp hyQ
    have hk : g * y * g⁻¹ * y⁻¹ ∈ K := hcent g hg y hyQ
    have hφk : φ ⟨g * y * g⁻¹ * y⁻¹, Q.mul_mem hgyQ (Q.inv_mem hyQ)⟩ = 1 :=
      (commutatorMapHom_eq_one_iff_mem_centralizer hZc hcZ
        (Q.mul_mem hgyQ (Q.inv_mem hyQ))).mpr hk.2
    have h1 : φ ⟨g * y * g⁻¹, hgyQ⟩ = φ ⟨y, hyQ⟩ := by
      have hsub : (⟨g * y * g⁻¹ * y⁻¹, Q.mul_mem hgyQ (Q.inv_mem hyQ)⟩ : ↥Q) =
          ⟨g * y * g⁻¹, hgyQ⟩ * ⟨y, hyQ⟩⁻¹ := rfl
      have hprod : φ (⟨g * y * g⁻¹, hgyQ⟩ * ⟨y, hyQ⟩⁻¹) = 1 := by
        rw [← hsub]
        exact hφk
      have h' : φ ⟨g * y * g⁻¹, hgyQ⟩ * (φ ⟨y, hyQ⟩)⁻¹ = 1 := by
        simpa [map_mul, map_inv] using hprod
      exact mul_inv_eq_one.mp h'
    have h2 : φ ⟨g * y * g⁻¹, hgyQ⟩ = g * φ ⟨y, hyQ⟩ * g⁻¹ :=
      commutatorMap_conj hZc hHQ hcQ hc hg hyQ
    have hgz : g * z * g⁻¹ = z := by
      calc
        g * z * g⁻¹ = g * φ ⟨y, hyQ⟩ * g⁻¹ := by rw [← hφy']
        _ = φ ⟨g * y * g⁻¹, hgyQ⟩ := h2.symm
        _ = φ ⟨y, hyQ⟩ := h1
        _ = z := hφy'
    rw [Subgroup.mem_bot]
    rw [hgz]
    group

end CFSG.Quasithin.Stroth
end
