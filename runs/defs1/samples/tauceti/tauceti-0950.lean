public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {ι : Type u} [Fintype ι] {n : ℕ} (h : Fintype.card ι = n + 1)
  (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, sphere (0 : EuclideanSpace ℝ ι) 1))

/-- A cell of `Sⁿ`, as a cell of `Sⁿ ∪_f Dⁿ⁺¹`. -/
def sphereMappingConeSphereCell {m : ℕ}
    (i : letI := sphereCWComplex h; cell (sphere (0 : EuclideanSpace ℝ ι) 1) m) :
    letI := sphereMappingConeCWComplex h f
    cell (sphereMappingCone f) m :=
  Sum.inl i

end TauCeti
end
end
