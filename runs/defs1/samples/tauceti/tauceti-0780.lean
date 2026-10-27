public section

namespace TauCeti

open MvPolynomial

namespace GridPentagonBetween

variable {n : ℕ} {a s : Fin n} {x y : GridState n}

/-- Regard an oriented rectangle as a pentagon: its terminal side must be the grid line replaced
by `γ`, and the turn row must lie among the rows that side spans. -/
def ofRightEq {u v : GridState n} (r : GridRectangleBetween u v)
    (hright : r.right = finRotate n a) (hs : s ∈ Grid.cIco r.bottom r.top) :
    GridPentagonBetween a s u v where
  toGridRectangleBetween := r
  right_eq := hright
  turn_mem := hs

end GridPentagonBetween
end TauCeti
end
