@[expose] public section

open scoped BigOperators

namespace O3

@[simp] theorem abovePhaseTrace_length {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    (abovePhaseTrace oracle y accelerated).length = 2 * N := by
  simp [abovePhaseTrace]
  omega

end O3
end
