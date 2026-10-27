public section

namespace CFSG.CGT.Stroth77

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

section Centre

variable {V : Type*} [CommGroup V] [Finite V]

theorem commRange_eq_of_tvCentre_eq {g h : MulAut V} (hg : Nat.card (commMap g).range = 2)
    (hh : Nat.card (commMap h).range = 2) (heq : tvCentre g = tvCentre h) :
    (commMap g).range = (commMap h).range := by
  ext x
  rw [mem_commRange_iff hg, mem_commRange_iff hh, heq]

end Centre
end CFSG.CGT.Stroth77
end
