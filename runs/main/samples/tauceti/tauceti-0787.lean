public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

noncomputable section

namespace Quiver.IsAcyclic

theorem length_lt_card (h : Quiver.IsAcyclic V) [Fintype V] {a b : V} (p : _root_.Quiver.Path a b) :
    p.length < Fintype.card V := by
  -- The bound is unfolded by hand rather than by `simpa`: `Quiver.IsAcyclic.card_path_self` puts
  -- `Nat.card` in scope for this file, and simp then exceeds `maxRecDepth` on this goal.
  have hle := List.Nodup.length_le_card (h.vertices_nodup p)
  rw [_root_.Quiver.Path.vertices_length] at hle
  omega

end Quiver.IsAcyclic
end
end TauCeti
end
