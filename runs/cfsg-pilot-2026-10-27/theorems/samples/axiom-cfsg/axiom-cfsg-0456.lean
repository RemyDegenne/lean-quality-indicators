public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Comm

variable {S : Type} [Group S]

theorem commSub_le_fix (K : Subgroup S) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hexp : ∀ x ∈ K, x * x = 1) (g : S) (hKg : ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    (hg2 : ∀ y ∈ K, g * g * y = y * (g * g)) :
    commSub K hKab g hKg ≤ K ⊓ Subgroup.centralizer ({g} : Set S) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_commSub K hKab g hKg x).mp hx
  refine ⟨K.mul_mem (hKg _ hy) (K.inv_mem hy), ?_⟩
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hu : g * y⁻¹ * g⁻¹ ∈ K := hKg _ (K.inv_mem hy)
  have hyu : (y * (g * y⁻¹ * g⁻¹)) * (y * (g * y⁻¹ * g⁻¹)) = 1 :=
    hexp _ (K.mul_mem hy hu)
  have hgy : g * g * y * g⁻¹ * g⁻¹ = y := by
    rw [hg2 y hy]
    group
  have key : g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ = 1 := by
    have e : g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ =
        (g * g * y * g⁻¹ * g⁻¹) * (g * y⁻¹ * g⁻¹) *
          (y * (g * y⁻¹ * g⁻¹)) := by group
    rw [e, hgy]
    exact hyu
  calc (g * y * g⁻¹ * y⁻¹) * g
      = (g * (g * y * g⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹)⁻¹ *
          (g * (g * y * g⁻¹ * y⁻¹)) := by group
    _ = g * (g * y * g⁻¹ * y⁻¹) := by rw [key]; group

end Comm
end CFSG.EvenSporadicStandard.Fin76b
end
