public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup

open scoped commutatorElement

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] (θ : ↥A →* P)

variable {θ} {S : Subgroup P}

theorem liftSub_mono {S' : Subgroup P} (h : S ≤ S') : liftSub θ S ≤ liftSub θ S' :=
  fun _ hx => by
    obtain ⟨hxA, hxS⟩ := mem_liftSub.1 hx
    exact mem_liftSub.2 ⟨hxA, h hxS⟩

end Lift
end CFSG.ComponentClassification.RankTwoClassical
end
