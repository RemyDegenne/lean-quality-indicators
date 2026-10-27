@[expose] public section

namespace TriangleInflation

open Finset

noncomputable
section

attribute [instance] TriangleModel.fintypeX TriangleModel.fintypeY TriangleModel.fintypeZ

/-- The response law of a party: probability `q` of the outcome `0 = false`. -/
def respMass (q : ℝ) : Bool → ℝ := fun b => if b then 1 - q else q

end
end TriangleInflation
end
