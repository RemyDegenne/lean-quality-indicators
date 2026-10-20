namespace P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd

set_option synthInstance.maxHeartbeats 1600000

set_option maxSynthPendingDepth 3

attribute [-instance] Quotient.instLE_mathlib

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_TorsionCollapseCrossEquation

open Finset

namespace M4aLocalCFT

universe u

variable {A : Type u} [AddCommGroup A]

namespace HerbrandPair

noncomputable def restrictToSubgroup (P : HerbrandPair A) (S : AddSubgroup A)
    (hd : ∀ a ∈ S, P.derive a ∈ S) (hn : ∀ a ∈ S, P.norm a ∈ S) :
    HerbrandPair S where
  derive :=
    { toFun := fun a => ⟨P.derive a.1, hd a.1 a.2⟩
      map_zero' := Subtype.ext (map_zero P.derive)
      map_add' := fun a b => Subtype.ext (map_add P.derive a.1 b.1) }
  norm :=
    { toFun := fun a => ⟨P.norm a.1, hn a.1 a.2⟩
      map_zero' := Subtype.ext (map_zero P.norm)
      map_add' := fun a b => Subtype.ext (map_add P.norm a.1 b.1) }
  derive_norm a := Subtype.ext (P.derive_norm a.1)
  norm_derive a := Subtype.ext (P.norm_derive a.1)

end HerbrandPair
end M4aLocalCFT
end Fold_TorsionCollapseCrossEquation
end P2MW.S_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
