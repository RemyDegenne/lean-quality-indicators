@[expose] public section

universe u

open CategoryTheory Limits FintypeCat Functor

attribute [local instance] FintypeCat.discreteTopology

namespace LightProfinite

variable {F : ℕᵒᵖ ⥤ FintypeCat.{u}} (c : Cone <| F ⋙ toLightProfinite)

open Extend

section LightProfiniteAsLimit

variable (S : LightProfinite.{u})

/-- A cone over `S.diagram'` whose cone point is `S`. -/
def asLimitCone' : Cone (S.diagram') := cone (𝟭 _) S

end LightProfiniteAsLimit
end LightProfinite
end
