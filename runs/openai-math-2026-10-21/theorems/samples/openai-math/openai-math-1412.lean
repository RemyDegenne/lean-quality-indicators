namespace OAI

namespace MUB6.Certificate.GramData.Block1

open Matrix

open scoped BigOperators

theorem entry_20_3 : Z 20 3 =
    ∑ k : Fin 21, lowerUnit entries k 20 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block1
end OAI
