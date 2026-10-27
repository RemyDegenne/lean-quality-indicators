@[expose] public section

namespace CoxeterMatrix

variable {B : Type*}

variable {B' : Type*} (e : B ≃ B') (M : CoxeterMatrix B)

variable (n : ℕ)

/-- The Coxeter matrix of type I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
protected def I (m : ℕ) : CoxeterMatrix (Fin 2) where
  M := Matrix.of fun i j => if i = j then 1 else m + 2
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by simp

end CoxeterMatrix
end
