set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uX uY uR uG

variable {X : Type uX} {Y : Type uY} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] {R : Type uR}

section Ring

variable [Ring R]

theorem rectangularUpperUnit_mem_elementarySubgroup (C : Matrix X Y R) :
    rectangularUpperUnit C ∈ elementarySubgroup (X ⊕ Y) R := by
  refine Matrix.induction_on' C ?_ ?_ ?_
  · rw [rectangularUpperUnit_zero]
    exact (elementarySubgroup (X ⊕ Y) R).one_mem
  · intro P Q hP hQ
    rw [rectangularUpperUnit_add]
    exact (elementarySubgroup (X ⊕ Y) R).mul_mem hP hQ
  · intro i j c
    rw [rectangularUpperUnit_single]
    exact elementaryUnit_mem _ _ _ _

end Ring
end Matrix.GeneralLinearGroup
end
