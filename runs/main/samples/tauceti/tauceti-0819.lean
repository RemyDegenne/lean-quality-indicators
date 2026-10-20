public section

open AddSubgroup

variable {A ι κ ν : Type*}

section AddGroup

variable [AddGroup A]

namespace AddSubgroup

section Hamming

variable [DecidableEq A] [Fintype ι] [Fintype κ]

@[simp]
theorem hammingDist_directSumEquivProd_symm (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x x' : C) (y y' : D) :
    hammingDist ((C.directSumEquivProd D).symm (x, y) : ι ⊕ κ → A)
        ((C.directSumEquivProd D).symm (x', y') : ι ⊕ κ → A) =
      hammingDist x.1 x'.1 + hammingDist y.1 y'.1 := by
  rw [← TauCeti.hammingDist_sumElim x.1 x'.1 y.1 y'.1]
  apply congrArg₂ hammingDist
  · funext i
    cases i <;> simp
  · funext i
    cases i <;> simp

end Hamming
end AddSubgroup
end AddGroup
end
