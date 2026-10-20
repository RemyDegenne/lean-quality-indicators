public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint}

variable [Fintype Point] [DecidableEq Region] [Fintype Region]

open scoped Classical in
variable (H) in
/-- The relative Maslov grading `gr(x, y) = μ(D) - 2 n_z(D)` of two generators, for a chosen
domain `D` from `x` to `y`, or `0` when no domain joins them. In a singly pointed diagram
satisfying the Euler normalization, when the periodic domains have Maslov index zero at the
source generator, the value does not depend on the choice of `D`
(`TauCeti.HeegaardRegionSystem.IsDomainBetween.relativeGrading_eq`). -/
noncomputable def relativeGrading (χ : Region → ℤ) (z : Basepoint) (x y : H.Generator) : ℚ :=
  if h : ∃ D, H.IsDomainBetween x y D then
    H.maslovIndex χ x y h.choose - 2 * h.choose (H.basepoint z)
  else 0

end HeegaardRegionSystem
end TauCeti
end
