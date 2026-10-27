public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The side data of the recut of a decomposition whose two rectangles share their initial side
column. -/
def IsRecutOfLeftEqLeft (D E : GridRectangleDecomposition x z) : Prop :=
  D.first.left = D.second.left ∧
    E.first.right = D.second.right ∧ E.second.right = D.first.right ∧
      ((D.first.right ∈ Grid.cIoo D.first.left D.second.right ∧
          E.middle = x.swapColumns D.first.right D.second.right ∧
            E.first.left = D.first.right ∧ E.second.left = D.first.left) ∨
        (D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
          E.middle = x.swapColumns D.first.left D.second.right ∧
            E.first.left = D.first.left ∧ E.second.left = D.second.right))

end GridRectangleDecomposition
end TauCeti
end
