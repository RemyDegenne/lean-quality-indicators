public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Clauses

variable {X : Type} [Group X] {Y : Subgroup X}

theorem indAut_congr' (e : ↥Y ≃* F42C) {a b : X} (h : a = b) (ha : a ∈ Nor Y) (hb : b ∈ Nor Y) :
    indAut e ha = indAut e hb := by
  subst h
  rfl

end Clauses
end CFSG.RankThree.PartTwo.Sec21.FF81.F4
end
