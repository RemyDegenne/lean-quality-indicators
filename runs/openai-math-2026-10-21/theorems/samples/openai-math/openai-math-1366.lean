namespace OAI

namespace CriticalStrip.Diagram

noncomputable section

open Finset

theorem Realizes.last_eq {n : ℕ} {p q : Pairing (n+1)} {t : Configuration (n+1)}
    (h : Realizes p q t) : t (Fin.last n) = lastTile p q := by
  classical
  have hn := h.north (Fin.last n) rfl
  have hw := h.west (Fin.last n)
  have he := h.east (Fin.last n)
  unfold lastTile
  generalize t (Fin.last n) = a at hn hw he ⊢
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]

end
end CriticalStrip.Diagram
end OAI
