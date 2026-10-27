public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open Multiplicative

section Split

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem GGConfig.card_bstar_centralizer_le {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p := by
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hE : IsElemAbelian p (Bs ⊓ Subgroup.centralizer (L : Set G)) :=
    IsElemAbelian.mono hcfg.2.1.2.1 inf_le_left
  exact card_le_of_isElemAbelian_of_cyclic hp hE
    (hS.2.2.2.2 _ inf_le_right (IsElemAbelian.isPGroup hE))

end Split
end CFSG.StandardType
end
