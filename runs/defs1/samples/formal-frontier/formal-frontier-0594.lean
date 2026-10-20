@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- The integers as a module over themselves, used as coefficients for affine
simplicial chains. -/
abbrev affineIntegerCoefficients : ModuleCat ℤ := ModuleCat.of ℤ ℤ

end Convexity.StdSimplex
end
end
