@[expose] public section

namespace BeyondBethe

open Complexity

/-- The canonical line-sum request encoding the mode, dimension, fixed index, and rational
vector. -/
def machineBetheLineSumCanonicalWord {m : ℕ} (rowMode : Bool)
    (fixed : Fin m) (y : Fin (m * m) → ℚ) : List Bool :=
  pair [rowMode]
    (pair (List.replicate m true)
      (pair (List.replicate fixed.1 true)
        (rationalFiniteVectorCode y)))

end BeyondBethe
end
