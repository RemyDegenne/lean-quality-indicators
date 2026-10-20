public section

namespace TauCeti

namespace GridInitialPentagonBetween

variable {n : ℕ} {a s t : Fin n} {x y z : GridState n}

@[simp]
theorem recutRectangleHexagon_hexagon_isLeft
    (P : GridInitialPentagonBetween a s x y) (Q : GridInitialPentagonBetween a t y z)
    (hcol : P.right ∈ Grid.cIoo (finRotate n a) Q.right)
    (hP : P.IsEmpty) (hQ : Q.IsEmpty) :
    (P.recutRectangleHexagon Q hcol hP hQ).hexagon.isLeft = false := (rfl)

end GridInitialPentagonBetween
end TauCeti
end
