public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.LeviQuot CFSG.Timmesfeld.ARS.NaturalModule

open scoped Matrix

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)

include S htY

theorem sup_corrN_inf_centralizer_eq [Finite G] (hq : 4 ≤ Nat.card A)
    (hpts : PointsDetermined Δ) :
    A ⊔ B ⊔ (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) =
      corrL A E t := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le (sup_le le_corrL S.le_corrL_right)
    (S.corrN_inf_centralizer_le_corrL htY hq)) ?_
  have h1 := card_mul_card_le_card_sup (H := A ⊔ B)
    (K := corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G))
    (by rw [inf_comm]; exact S.corrN_inf_centralizer_inf_sup_eq_bot)
  have h2 : Nat.card A * Nat.card A ≤ Nat.card ↥(A ⊔ B) := by
    have := card_mul_card_le_card_sup (S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne)
    rwa [S.cls.root.card_eq S.tri.memB S.tri.memA] at this
  rw [S.card_corrL htY hq hpts]
  calc Nat.card A ^ 3 = Nat.card A * Nat.card A *
        Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) := by
        rw [S.card_corrN_inf_centralizer_eq htY hq hpts]
        ring
    _ ≤ Nat.card ↥(A ⊔ B) *
        Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) :=
        Nat.mul_le_mul_right _ h2
    _ ≤ _ := h1

end TriangleSetting
end CFSG.Timmesfeld.Transvection
end
