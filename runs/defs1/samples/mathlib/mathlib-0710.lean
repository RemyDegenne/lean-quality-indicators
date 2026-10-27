@[expose] public section

noncomputable section

universe u v w x

variable {F : Type*} {X : Type u} {Y : Type v} {Z : Type w} {Z' : Type x} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace Z']

open unitInterval

namespace ContinuousMap

namespace HomotopyWith

variable {P : C(X, Y) → Prop}

/-- Casting a `HomotopyWith f₀ f₁ P` to a `HomotopyWith g₀ g₁ P` where `f₀ = g₀` and `f₁ = g₁`.
-/
@[simps!]
def cast {f₀ f₁ g₀ g₁ : C(X, Y)} (F : HomotopyWith f₀ f₁ P) (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) :
    HomotopyWith g₀ g₁ P where
  toHomotopy := F.toHomotopy.cast h₀ h₁
  prop' := F.prop

end HomotopyWith
end ContinuousMap
end
end
