public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

namespace B48Om

theorem mem_inf_of_commute {G : Type} [Group G] {p : ℕ} {B Bs N : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center ↥N = ⊥)
    (hinner : ∀ b ∈ Bs, ∃ g ∈ N, ∀ k ∈ N, b * k * b⁻¹ = g * k * g⁻¹) {t : G} (htN : t ∈ N)
    (htC : t ∈ Subgroup.centralizer ((Bs ⊓ N : Subgroup G) : Set G)) (htp : t ^ p = 1) :
    t ∈ Bs ⊓ N := by
  refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 t ?_ htp, htN⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨g, hgE, hc⟩ := exists_mem_inf_mul hBs hZ hinner b hb
  have htg : g * t = t * g := Subgroup.mem_centralizer_iff.mp htC g hgE
  have htc : t * (g⁻¹ * b) = (g⁻¹ * b) * t := Subgroup.mem_centralizer_iff.mp hc t htN
  calc b * t = g * ((g⁻¹ * b) * t) := by group
    _ = g * (t * (g⁻¹ * b)) := by rw [htc]
    _ = (g * t) * (g⁻¹ * b) := by group
    _ = (t * g) * (g⁻¹ * b) := by rw [htg]
    _ = t * b := by group

end B48Om
end CFSG.StandardType
end
