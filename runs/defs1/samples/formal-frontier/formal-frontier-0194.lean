@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The universe-zero coefficient object is canonically the ordinary integer
module. -/
def singularHomologyIntegerCoefficientsIso :
    singularHomologyIntegerCoefficients.{0} ≅ ModuleCat.of ℤ ℤ :=
  ULift.moduleEquiv.toModuleIso

end TopCat
end
end
