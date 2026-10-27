public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.SectionRank.EvenCover Subgroup

theorem false_of_odd_cover_trivial {X K : Type*} [Group X] [Finite X] [Group K]
    (h3 : Nat.card (Subgroup.center X) = 3) (e : X ⧸ Subgroup.center X ≃* K)
    (H : ∀ π : X →* K, Function.Surjective π → π.ker ≤ Subgroup.center X →
      Odd (Nat.card π.ker) → π.ker = ⊥) : False := by
  have hker := ker_comp_mk'_center_eq e
  have hbot := H _ (surjective_comp_mk'_center e) hker.le (by rw [hker, h3]; decide)
  rw [hker] at hbot
  rw [hbot, Subgroup.card_bot] at h3
  omega

end CFSG.QuasithinUnique.Ch1
end
