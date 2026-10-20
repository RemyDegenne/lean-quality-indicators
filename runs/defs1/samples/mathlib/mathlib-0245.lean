@[expose] public section

noncomputable section

open Affine

open Set

open scoped Pointwise

section affineSpan

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- The affine span of a set of points is the smallest affine subspace containing those points.
(Actually defined here in terms of spans in modules.) -/
def affineSpan (s : Set P) : AffineSubspace k P where
  carrier := spanPoints k s
  smul_vsub_vadd_mem' c _ _ _ hp₁ hp₂ hp₃ :=
    vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp₃
      ((vectorSpan k s).smul_mem c
        (vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints k hp₁ hp₂))

end affineSpan
end
end
