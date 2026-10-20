public section

namespace TauCeti

namespace FundamentalGroup

open Path.Homotopic

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable {x : X} {y : Y} {z : Z}

theorem mapOfEq_congr {f₁ f₂ : C(X, Y)} (hfe : f₁ = f₂) (h₁ : f₁ x = y) (h₂ : f₂ x = y)
    (p : _root_.FundamentalGroup X x) :
    _root_.FundamentalGroup.mapOfEq f₁ h₁ p = _root_.FundamentalGroup.mapOfEq f₂ h₂ p := by
  subst hfe
  rfl

end FundamentalGroup
end TauCeti
end
