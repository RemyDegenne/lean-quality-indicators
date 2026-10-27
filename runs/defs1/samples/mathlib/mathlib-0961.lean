@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- `IsSplitMono f` is the assertion that `f` admits a retraction -/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitMono : Nonempty (SplitMono f)

end CategoryTheory
end
