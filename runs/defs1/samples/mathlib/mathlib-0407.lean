@[expose] public section

open Opposite

universe v v₁ v₂ u u₁ u₂

infixr:10 " ⟶ " => Quiver.Hom

namespace Quiver

/-- A quiver is thin if it has no parallel arrows. -/
abbrev IsThin (V : Type u) [Quiver V] : Prop := ∀ a b : V, Subsingleton (a ⟶ b)

end Quiver
end
