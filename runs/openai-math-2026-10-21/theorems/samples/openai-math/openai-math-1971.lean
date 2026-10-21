namespace OAI

namespace MUB6.Certificate.GramData.Block4

open Matrix

open scoped BigOperators

theorem entry_16_11 : Z 16 11 =
    ∑ k : Fin 22, lowerUnit entries k 16 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block4
end OAI
