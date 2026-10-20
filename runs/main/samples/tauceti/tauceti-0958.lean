public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

theorem pentagon_left_eq_column_of_mem_rectanglePentagonSameSideOrder (x : GridState n)
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x x)
    (hD : D ∈ G.rectanglePentagonSameSideOrder C x) :
    D.pentagon.left = C.column := by
  have hmem := (G.mem_rectanglePentagonSameSideOrder C x D).1 hD
  have hcount := (G.mem_rectanglePentagonDecompositions C D).1 hmem.1
  have hempty : D.rectangle.IsEmpty ∧ D.pentagon.IsEmpty :=
    ⟨((G.mem_unblockedRectangles D.rectangle).1 hcount.1).1,
      ((G.mem_pentagons D.pentagon).1 hcount.2).1⟩
  have hadj :=
    (D.rectangle.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
      D.pentagon.toGridRectangleBetween hmem.2.1.symm).1 hempty
  apply (finRotate n).injective
  calc
    finRotate n D.pentagon.left = finRotate n D.rectangle.left :=
      congrArg (finRotate n) hmem.2.1.symm
    _ = D.rectangle.right := hadj.symm
    _ = D.pentagon.right := hmem.2.2
    _ = finRotate n C.column := D.pentagon.right_eq

end GridDiagram
end TauCeti
end
