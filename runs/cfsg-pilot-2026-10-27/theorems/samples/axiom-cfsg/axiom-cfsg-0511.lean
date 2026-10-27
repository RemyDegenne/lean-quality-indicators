public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open S2MathAs51642Interfaces

theorem GGResHyp.card_automizer_L_of_e8_two
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs L) :
    Nat.card (ggAutomizer L Bs) = 696729600 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, _, _, ι, φ, h, α, _, _, _, ⟨e, _⟩, _⟩ :=
    e78_e8_actual_module hH (hL.mono_label fun _ h => ⟨rfl, h⟩)
  exact (Nat.card_congr e.toEquiv).symm.trans card_coxeterE8_group

end CFSG.StandardType
end
