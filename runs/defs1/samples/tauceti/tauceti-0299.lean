public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval TauCeti.TopCat

namespace TauCeti.HurewiczOne

local notation "toI" => (StdSimplex.homeomorphI : C(StdSimplex ℝ (Fin 2), I))

local notation "ofI" => (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))

variable {X : TopCat.{0}}

variable (X) in
/-- The boundaries among the singular `1`-chains of `X`. -/
abbrev boundaries₁ : Submodule ℤ (((singularChains ℤ).obj X).X 1) :=
  LinearMap.range (((singularChains ℤ).obj X).d 2 1).hom

end TauCeti.HurewiczOne
end
end
