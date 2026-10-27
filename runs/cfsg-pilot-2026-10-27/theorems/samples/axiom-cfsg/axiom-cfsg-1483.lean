public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG

open scoped Matrix

variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

theorem card_pairMod_four : Nat.card (PairMod (Fin 4) (ZMod 2)) = 2 ^ 8 := by
  rw [Nat.card_prod, card_stdMod_four]
  rfl

end A7
end H
end CFSG.Quasithin
end
