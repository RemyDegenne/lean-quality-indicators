namespace OAI

namespace Erdos970

namespace ErdosLatticeChain

theorem vector_card_bound_actual (V : Finset (ℕ × ℕ)) :
    (V.card : ℝ) ≤ 5*(1+(totalLength V : ℝ)^((2 : ℝ)/3)) :=
  vector_card_bound V (Nat.cast_nonneg _) le_rfl

end ErdosLatticeChain
end Erdos970
end OAI
