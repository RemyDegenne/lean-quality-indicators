set_option warningAsError true

@[expose] public section

namespace Matrix

universe uX uY uR

section Ring

variable {R : Type uR} [Ring R]

theorem fromBlocks_elementary_reduce {X : Type uX} {Y : Type uY}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : Matrix X X R) (B : Matrix X Y R) (C : Matrix Y X R) (D : Matrix Y Y R)
    [Invertible A] :
    ∃ L Q : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R,
      ((L : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) *
          Matrix.fromBlocks A B C D *
        ((Q : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) =
          Matrix.fromBlocks A 0 0 (D - C * ⅟A * B) := by
  let L : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R :=
    ⟨GeneralLinearGroup.rectangularLowerUnit (-(C * ⅟A)),
      GeneralLinearGroup.rectangularLowerUnit_mem_elementarySubgroup _⟩
  let Q : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R :=
    ⟨GeneralLinearGroup.rectangularUpperUnit (-(⅟A * B)),
      GeneralLinearGroup.rectangularUpperUnit_mem_elementarySubgroup _⟩
  refine ⟨L, Q, ?_⟩
  change (GeneralLinearGroup.rectangularLowerUnit (-(C * ⅟A)) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) * Matrix.fromBlocks A B C D *
        (GeneralLinearGroup.rectangularUpperUnit (-(⅟A * B)) :
          Matrix (X ⊕ Y) (X ⊕ Y) R) = _
  rw [GeneralLinearGroup.rectangularLowerUnit_val,
    GeneralLinearGroup.rectangularUpperUnit_val]
  simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, Matrix.mul_neg,
    Matrix.neg_mul, sub_eq_add_neg, add_comm]
  simpa only [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul] using (add_neg_cancel B)

end Ring
end Matrix
end
