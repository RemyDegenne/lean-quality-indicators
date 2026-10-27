public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7.MS

variable {G : Type} [Group G]

section Letters3

open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem letters_P_gen (hF : HFacts H H₁ H₂ e) :
    ∀ p ∈ Psub e, ∃ i j : ℤ, e 0 ^ i * e 2 ^ j = p :=
  closure_pair_gen (show Commute (e 0) (e 2) from letters_comm02 hF)

end Letters3
end CFSG.GH74.QTGen4.Recog.G23.P7.MS
end
