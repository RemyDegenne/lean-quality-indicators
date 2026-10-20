public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V]

namespace Quiver

theorem IsSource_def (i : V) : IsSource i ↔ ∀ a : V, IsEmpty (a ⟶ i) :=
  Iff.rfl

end Quiver
end TauCeti
end
