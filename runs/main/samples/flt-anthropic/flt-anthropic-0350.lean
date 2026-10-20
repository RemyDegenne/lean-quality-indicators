namespace P2MW.S_CohCarrier_jDeg_diamondRaw_comm

set_option autoImplicit false

open scoped MatrixGroups

open Subgroup Subgroup.leftTransversals CohCarrier CongruenceSubgroup

namespace IharaMintJD

section NatInj

variable {G G' A : Type*} [Group G] [Group G'] [CommGroup A]

theorem index_comap_of_quotient_surjective (f : G' →* G) (K : Subgroup G) [K.FiniteIndex]
    (hsurj : Function.Surjective (comapQuotientMap f K)) :
    (K.comap f).index = K.index := by
  have e : G' ⧸ (K.comap f) ≃ G ⧸ K :=
    Equiv.ofBijective _ ⟨comapQuotientMap_injective f K, hsurj⟩
  simp only [Subgroup.index, Nat.card_congr e]

end NatInj
end IharaMintJD
end P2MW.S_CohCarrier_jDeg_diamondRaw_comm
