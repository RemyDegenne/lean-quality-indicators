public section

namespace TauCeti.GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recut a pentagon followed by a rectangle sharing their terminal side, when the rectangle's
initial side is inside the pentagon's column interval. The first recut rectangle inherits
the terminal side and contains the turn row, so the result is again a pentagon followed by
a rectangle. -/
noncomputable def recutTerminal (D : GridPentagonRectangleDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hcol : D.rectangle.left ∈ Grid.cIoo D.pentagon.left D.pentagon.right)
    (hp : D.pentagon.IsEmpty) (hr : D.rectangle.IsEmpty) :
    GridPentagonRectangleDecomposition a s x z where
  middle := (D.terminalRecut hcommon hcol hp hr).middle
  first := GridPentagonBetween.ofRightEq (D.terminalRecut hcommon hcol hp hr).first
    ((D.terminalRecut_data hcommon hcol hp hr).2.2.1.trans D.pentagon.right_eq)
    (D.terminalRecut_turn_mem hcommon hcol hp hr)
  second := (D.terminalRecut hcommon hcol hp hr).second

end TauCeti.GridPentagonRectangleDecomposition
end
