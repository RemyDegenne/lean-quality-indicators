public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice

theorem e8t3K_vec_ofFn (v : Fin Tag.E8.rank → ℤ) : e8t3K_vec (List.ofFn v) = v := by
  funext i
  simp [e8t3K_vec, List.getD_eq_getElem]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
end
