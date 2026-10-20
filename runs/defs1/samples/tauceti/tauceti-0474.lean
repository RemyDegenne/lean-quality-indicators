public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)

include hS

/-- The connecting map `Hⁿ⁰(X, M₃) →+ Hⁿ¹(X, M₁)` of the long exact cohomology sequence of a
short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules. -/
def cohomologyδ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Cohomology S.X₃ n₀ →+ Cohomology S.X₁ n₁ :=
  CategoryTheory.Sheaf.H.δ (shortExact_map_toSheaf hS) n₀ n₁ h

end Scheme.Modules
end
end AlgebraicGeometry
end TauCeti
end
