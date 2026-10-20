public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

variable (D : PDCode n) (h : Fin (4 * n)) (b : Bool)

@[simp] theorem reidemeisterOne_edgePair_inr_one :
    (D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n (.inr 1)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val h)) := by
  simp [reidemeisterOne_edgePair_val, Equiv.permCongr_apply, kinkPerm_inr_one]

end PDCode
end TauCeti
end
