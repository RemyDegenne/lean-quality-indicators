public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open

open scoped Pointwise

section Lifts

variable {K : Type} [Group K] [Finite K] {X : Type} [MulAction K X] [Finite X] [FaithfulSMul K X]

namespace HoltData

variable (D : HoltData K X) {i₀ : D.ι} (hι : ∀ j, j = i₀)

include hι in
theorem exists_commute_lifts (hK : IsStarGroup K X) {Z : Subgroup K} (hZ : IsPGroup 2 Z)
    {u₁ u₂ : K} (hu₁ : u₁ ∈ longInv K X) (hu₂ : u₂ ∈ longInv K X)
    (h12 : D.extRho hι u₁ * D.extRho hι u₂ = D.extRho hι u₂ * D.extRho hι u₁)
    (hZ₁ : ∀ z ∈ Z, D.extRho hι z * D.extRho hι u₁ = D.extRho hι u₁ * D.extRho hι z)
    (hZ₂ : ∀ z ∈ Z, D.extRho hι z * D.extRho hι u₂ = D.extRho hι u₂ * D.extRho hι z)
    {γ₀ : X} (hγ₀ : γ₀ ∈ fixSet X Z)
    (hγ₂ : D.extRho hι u₂ (D.coord γ₀ i₀) = D.coord γ₀ i₀) :
    ∃ x₁ x₂ : K, x₁ ∈ longInvAt K X γ₀ ∧ x₂ ∈ longInvAt K X γ₀ ∧ x₁ * x₂ = x₂ * x₁ ∧
      x₁ ∈ Subgroup.centralizer (Z : Set K) ∧ x₂ ∈ Subgroup.centralizer (Z : Set K) ∧
      D.extRho hι x₁ = D.extRho hι u₁ ∧ D.extRho hι x₂ = D.extRho hι u₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := jOddCore K X
  obtain ⟨y₁, hy₁, hy₁Z, hy₁ρ⟩ := D.exists_mem_centralizer_extRho_eq hι hK hZ hu₁ hZ₁
  obtain ⟨y₂, hy₂, hy₂Z, hy₂ρ⟩ := D.exists_mem_centralizer_extRho_eq hι hK hZ hu₂ hZ₂
  have hy₁y₁ := mul_self_eq_one_of_mem_longInv hy₁
  have hy₂y₂ := mul_self_eq_one_of_mem_longInv hy₂
  have hu₂u₂ := mul_self_eq_one_of_mem_longInv hu₂
  have hsq : (y₁ * y₂) ^ 2 ∈ O ⊓ Subgroup.centralizer (Z : Set K) := by
    have hconj : y₂ * y₁ * y₂ ∈ longInv K X := by
      have h := conj_mem_longInv hy₁ y₂
      rwa [inv_eq_self_of_mem_longInv hy₂] at h
    refine ⟨?_, pow_mem (mul_mem hy₁Z hy₂Z) 2⟩
    have h := D.mul_mem_jOddCore_of_extRho_eq hι hK hy₁ hconj (by
      rw [map_mul, map_mul, hy₁ρ, hy₂ρ, ← h12, mul_assoc, ← map_mul, hu₂u₂, map_one, mul_one])
    rwa [sq, show y₁ * y₂ * (y₁ * y₂) = y₁ * (y₂ * y₁ * y₂) by group]
  have hOZ : Odd (Nat.card ↥(O ⊓ Subgroup.centralizer (Z : Set K))) :=
    Odd.of_dvd_nat odd_card_jOddCore (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨p, hp, hpc⟩ := exists_mem_conj_commute_of_odd hOZ hy₁y₁ hy₂y₂ hsq
  set y₁' := p * y₁ * p⁻¹
  have hy₁' : y₁' ∈ longInv K X := conj_mem_longInv hy₁ p
  have hy₁'Z : y₁' ∈ Subgroup.centralizer (Z : Set K) :=
    mul_mem (mul_mem hp.2 hy₁Z) (inv_mem hp.2)
  have hy₁'ρ : D.extRho hι y₁' = D.extRho hι u₁ := by
    rw [map_mul, map_mul, map_inv, D.extRho_eq_one_of_mem_jOddCore hι hp.1, one_mul, inv_one,
      mul_one, hy₁ρ]
  obtain ⟨δ, hδ, hδu⟩ := hy₂.2
  have hδ₁ : y₁' • δ = δ := by
    refine hδu _ ?_
    show y₂ • y₁' • δ = y₁' • δ
    rw [← mul_smul, ← hpc.eq, mul_smul, hδ]
  have hδZ : δ ∈ fixSet X Z := fun z hz => hδu _ (by
    show y₂ • z • δ = z • δ
    rw [← mul_smul, ← (Subgroup.mem_centralizer_iff.mp hy₂Z z hz), mul_smul, hδ])
  have hδγ : D.coord δ = D.coord γ₀ := by
    funext j
    rw [hι j]
    have h1 : D.extRho hι u₂ (D.coord δ i₀) = D.coord δ i₀ := by
      rw [← hy₂ρ, D.extRho_coord, hδ]
    obtain ⟨-, c, -, hcu⟩ := D.rho_mem_longInv hu₂ i₀
    rw [← D.extRho_eq_rho hι] at hcu
    exact (hcu _ h1).trans (hcu _ hγ₂).symm
  obtain ⟨⟨g, hg⟩, hgδ⟩ := (D.coord_eq_iff δ γ₀).mp hδγ
  have hOodd : Odd (Nat.card O) := odd_card_jOddCore
  have hON : O.Normal := jOddCore_normal
  obtain ⟨m, hm, hmδ⟩ := exists_mem_centralizer_smul_eq (p := 2)
    (fun h => by rw [Nat.odd_iff] at hOodd; omega) hZ
    (fun x _ => Subgroup.mem_normalizer_iff.mpr fun n =>
      ⟨fun hn => hON.conj_mem n hn x, fun hn => by
        simpa [mul_assoc] using hON.conj_mem _ hn x⁻¹⟩)
    hδZ hγ₀ hg hgδ
  have hmρ : D.extRho hι m = 1 := D.extRho_eq_one_of_mem_jOddCore hι hm.1
  refine ⟨m * y₁' * m⁻¹, m * y₂ * m⁻¹, ⟨conj_mem_longInv hy₁' m, ?_⟩,
    ⟨conj_mem_longInv hy₂ m, ?_⟩, ?_, mul_mem (mul_mem hm.2 hy₁'Z) (inv_mem hm.2),
    mul_mem (mul_mem hm.2 hy₂Z) (inv_mem hm.2), ?_, ?_⟩
  · rw [← hmδ, mul_smul, mul_smul, inv_smul_smul, hδ₁]
  · rw [← hmδ, mul_smul, mul_smul, inv_smul_smul, hδ]
  · rw [show m * y₁' * m⁻¹ * (m * y₂ * m⁻¹) = m * (y₁' * y₂) * m⁻¹ by group, hpc.eq]
    group
  · rw [map_mul, map_mul, map_inv, hmρ, one_mul, inv_one, mul_one, hy₁'ρ]
  · rw [map_mul, map_mul, map_inv, hmρ, one_mul, inv_one, mul_one, hy₂ρ]

end HoltData
end Lifts
end CFSG.Holt.H78
end
