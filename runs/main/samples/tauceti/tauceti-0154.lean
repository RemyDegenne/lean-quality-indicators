public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ}

open ReidemeisterThree

variable (D : PDCode n) (c : Fin 3 ↪ Fin n)

theorem componentPerm_reidemeisterThree :
    (D.reidemeisterThree c).componentPerm =
      (reidemeisterThreePerm D c).permCongr D.componentPerm := by
  rw [componentPerm_def, componentPerm_def, Equiv.permCongr_mul,
    reidemeisterThreePerm_crossingTurn, reidemeisterThree_edgePair]
  simp only [crossingTurn_def, reidemeisterThree]

end TauCeti.PDCode
end
