noncomputable section

namespace SoficGroups

section

open Filter Topology

universe u v w

open scoped Pointwise commutatorElement symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)

end
end SoficGroups
end
