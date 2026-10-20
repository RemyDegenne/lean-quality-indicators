@[expose] public section

namespace BeyondBethe

open Complexity

theorem machineRationalDirectionUpdateMatrixInit_semantics {d : ℕ}
    (b : Fin d → ℚ) :
    machineRationalDirectionUpdateMatrixInit
        (rationalDirectionUpdateCanonicalWord b) =
      machineRationalDirectionUpdateMatrixSemanticState b 0 := by
  simp [machineRationalDirectionUpdateMatrixInit,
    machineRationalDirectionUpdateMatrixSemanticState,
    machineRationalDirectionUpdateMatrixIndices,
    rationalDirectionUpdateCanonicalWord,
    machineUnaryRangeCode_encode, finRangeUnaryCode,
    rationalDirectionUpdateRowsPrefix, binaryListCode]

end BeyondBethe
end
