@[expose] public section

noncomputable section

namespace ConwaySoifer.SevenTriangles

theorem formRotate120_vectorNormal_clockwise (p : Point) :
    formRotate120 (vectorNormal p) = vectorNormal (-rotateNeg60 p) := by
  rcases p with ⟨x, z⟩
  apply Prod.ext <;> dsimp [formRotate120, vectorNormal, rotateNeg60] <;> ring

end ConwaySoifer.SevenTriangles
end
end
