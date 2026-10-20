namespace P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso

set_option autoImplicit false

universe u

namespace DDTr

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped Matrix

section Generic

variable {q : ℕ} [Fact q.Prime]

variable {B : Type u} [CommRing B] {B' : Type u} [CommRing B']

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := by
  unfold Series.id
  exact MvFormalGroup.linearPart_X

end Generic
end DDTr
end P2MW.S_CerednikDrinfeld_FormalODModule_isHomogeneousVBasis_map_and_hasStructureConstants_map_of_hom_of_isIso
