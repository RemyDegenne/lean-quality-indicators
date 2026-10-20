@[expose] public section

namespace NormedSpace

open FormalMultilinearSeries

section TopologicalAlgebra

variable (𝕂 𝔸 : Type*) [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]

variable {𝕂 𝔸}

open scoped Classical in
/-- `NormedSpace.log : 𝔸 → 𝔸` is the logarithm `log x = ∑ₙ ((-1) ^ (n + 1) / n) • (x - 1) ^ n`.
It is defined as the sum of the `FormalMultilinearSeries` `logSeries ℚ 𝔸` at `x - 1`, in the same
way as `NormedSpace.exp`, and takes the junk value `0` where the series does not converge.

If `𝔸` can't be equipped with a `ℚ`-algebra structure, we use the junk value `0`.
-/
noncomputable irreducible_def log (x : 𝔸) : 𝔸 :=
  if h : Nonempty (Algebra ℚ 𝔸) then
    letI _ := h.some
    (NormedSpace.logSeries ℚ 𝔸).sum (x - 1)
  else
    0

end TopologicalAlgebra
end NormedSpace
end
