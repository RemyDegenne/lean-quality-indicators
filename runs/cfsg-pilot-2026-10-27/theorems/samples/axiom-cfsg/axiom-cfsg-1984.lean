public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

namespace AscModel

variable (m : AscModel z)

include m

theorem not_conj_mem_V [Finite G] (hyp : Asc03Hyp G z) {g : G} (hgz : g * z * g⁻¹ ≠ z)
    (hsQ : g * z * g⁻¹ ∈ ascQ z) {w : G} (hwQ : w ∈ ascQ z) (hwF : w ∉ m.fSub) (a : G) :
    a⁻¹ * w * a ∉ m.ascV hyp hgz hsQ := by
  intro hmem
  have hF' : a⁻¹ * w * a ∈ m.fSub := m.ascV_le_fSub hyp hgz hsQ hmem
  by_cases h1 : a⁻¹ * w * a = 1
  · apply hwF
    have : w = 1 := by
      calc w = a * (a⁻¹ * w * a) * a⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact one_mem _
  · obtain ⟨c, hc⟩ := (m.conj_mem_Q_iff hyp (m.fSub_le_ascQ hyp hF') h1).2 hF'
    have : (a * c) * z * (a * c)⁻¹ = w := by
      calc (a * c) * z * (a * c)⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by group
        _ = a * (a⁻¹ * w * a) * a⁻¹ := by rw [hc]
        _ = w := by group
    exact hwF (m.zconj_mem_fSub hyp hwQ (isConj_iff.2 ⟨a * c, this⟩))

end AscModel
end CFSG.Quasithin
end
