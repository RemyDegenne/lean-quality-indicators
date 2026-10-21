namespace OAI

namespace MUB6.Certificate.GramData.Block1

open Matrix

open scoped BigOperators

theorem entry_15_0 : Z 15 0 =
    ∑ k : Fin 21, lowerUnit entries k 15 * D k * lowerUnit entries k 0 := by
  decide +kernel

end MUB6.Certificate.GramData.Block1
end OAI
