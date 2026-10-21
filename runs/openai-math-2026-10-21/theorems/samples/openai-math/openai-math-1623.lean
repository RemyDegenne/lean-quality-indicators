namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl

open ExpanderTables

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

end UniqueGamesTheorem.Foundations.PCP.ExpanderRowControl
end
end OAI
