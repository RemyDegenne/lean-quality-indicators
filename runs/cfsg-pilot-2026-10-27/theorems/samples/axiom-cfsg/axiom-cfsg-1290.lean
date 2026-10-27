public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu CFSG.Monster.Code MulAction

open scoped Pointwise commutatorElement

namespace ResM24

variable {G : Type} [Group G] [Finite G] {z : G} {c : Loc49 G z} (ρ : ResM24 c)

theorem preFixOct_eq_sup (hS : FixOctSym) : ρ.preFixOct = c.K ⊔ c.E := by
  have hle : c.K ⊔ c.E ≤ ρ.preFixOct := sup_le (ρ.K_le_preFixOct hS) ρ.E_le_preFixOct
  have h4 : c.K.relIndex c.E = 4 := by
    change ((c.K).subgroupOf c.E).index = 4
    have hsub : (c.E ⊓ c.K).subgroupOf c.E = c.K.subgroupOf c.E := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    rw [← hsub]
    exact c.index_E_inf_K
  have hKE : c.K.relIndex (c.K ⊔ c.E) = 4 := by
    haveI : (c.K.subgroupOf c.G12).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer c.K_le_G12).2
        (fun g hg => c.mem_normalizer_K (c.G12_le_G2 hg))
    have h2 := Subgroup.relIndex_sup_right (H := c.E.subgroupOf c.G12)
      (K := c.K.subgroupOf c.G12)
    rw [← Subgroup.subgroupOf_sup c.E_le_G12 c.K_le_G12,
      Subgroup.relIndex_subgroupOf c.E_le_G12] at h2
    have h2' : (c.K.subgroupOf c.G12).relIndex
        ((c.E ⊔ c.K).subgroupOf c.G12) = 4 := by
      rw [h2, h4]
    have h1 := Subgroup.relIndex_subgroupOf (H := c.K) (K := c.E ⊔ c.K) (L := c.G12)
      (sup_le c.E_le_G12 c.K_le_G12)
    calc c.K.relIndex (c.K ⊔ c.E) = c.K.relIndex (c.E ⊔ c.K) := by rw [sup_comm]
      _ = (c.K.subgroupOf c.G12).relIndex ((c.E ⊔ c.K).subgroupOf c.G12) := h1.symm
      _ = 4 := h2'
  have hsupidx : (c.K ⊔ c.E).relIndex c.G12 = 6 := by
    have h := Subgroup.relIndex_mul_relIndex (H := c.K) (K := c.K ⊔ c.E) (L := c.G12)
      le_sup_left (sup_le c.K_le_G12 c.E_le_G12)
    rw [c.index_K_G12, hKE] at h
    omega
  have hcard : Nat.card ↥ρ.preFixOct = Nat.card ↥(c.K ⊔ c.E) := by
    have h1 := Subgroup.card_mul_index (ρ.preFixOct.subgroupOf c.G12)
    have h2 := Subgroup.card_mul_index ((c.K ⊔ c.E).subgroupOf c.G12)
    have hpre : Nat.card ↥(ρ.preFixOct.subgroupOf c.G12) = Nat.card ↥ρ.preFixOct :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe ρ.preFixOct_le_G12).toEquiv
    have hsup : Nat.card ↥((c.K ⊔ c.E).subgroupOf c.G12) =
        Nat.card ↥(c.K ⊔ c.E) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (sup_le c.K_le_G12 c.E_le_G12)).toEquiv
    rw [hpre, ρ.index_preFixOct hS] at h1
    rw [hsup] at h2
    change Nat.card ↥(c.K ⊔ c.E) *
      (c.K ⊔ c.E).relIndex c.G12 = Nat.card ↥c.G12 at h2
    rw [hsupidx] at h2
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

end ResM24
end CFSG.Quasithin.H13.AS91
end
