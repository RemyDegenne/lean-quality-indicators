public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.SteinbergBR

open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

theorem le_normalizer_of_not_dvd_card [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {V B : Subgroup (suzukiGroup a K)}
    (hV : IsPGroup 2 V) (hVi : ¬ 2 ∣ V.index) (hVB : V ≤ B)
    (hB : ¬ (2 ^ (2 * a + 1)) ^ 2 + 1 ∣ Nat.card B) :
    B ≤ Subgroup.normalizer (V : Set (suzukiGroup a K)) := by
  obtain ⟨g, hg⟩ := exists_mem_iff_conj_suzukiU ha hK hV hVi
  have hcard : Nat.card (suzukiOmegaSub hK) = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.2]
    exact Nat.card_coe_set_eq (suzukiOmega a K)
  have hstab := le_stabilizer_of_transitive_off
    (g • (⟨suzukiInfty K, suzukiInfty_mem_suzukiOmega a K⟩ : suzukiOmegaSub hK)) hVB
    (fun β γ hβ hγ => by
      obtain ⟨u, hu, huβ⟩ := exists_mem_smul_eq_of_conj_suzukiU hK hg β.2 γ.2
        (fun h => hβ (Subtype.ext h)) (fun h => hγ (Subtype.ext h))
      exact ⟨u, hu, Subtype.ext huβ⟩) (by rwa [hcard])
  intro b hb
  have hbω := (MulAction.mem_stabilizer_iff.1 (hstab hb))
  have hbB : g⁻¹ * b * g ∈ suzukiB a K := by
    rw [← (suzuki_ovoid_stabilizer hK).2, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hbω,
      inv_smul_smul]
  have hbN : g⁻¹ * b * g ∈ Subgroup.normalizer (suzukiU a K : Set (suzukiGroup a K)) :=
    sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK) hbB
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hg x, hg (b * x * b⁻¹), Subgroup.mem_normalizer_iff.1 hbN (g⁻¹ * x * g),
    show g⁻¹ * b * g * (g⁻¹ * x * g) * (g⁻¹ * b * g)⁻¹ = g⁻¹ * (b * x * b⁻¹) * g by group]

end CFSG.Quasithin.H13.NQCore
end
