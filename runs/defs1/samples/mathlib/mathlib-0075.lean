@[expose] public section

variable {l m n o : Type*} {R A : Type*}

section NonUnitalNonAssocSemiring

variable (R) [Fintype m]

section one_side

variable [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

section right

variable (l) [IsScalarTower R A A]

/-- A version of `LinearMap.mulRight` for matrix multiplication. -/
@[simps]
def mulRightLinearMap (Y : Matrix m n A) :
    Matrix l m A →ₗ[R] Matrix l n A where
  toFun := (· * Y)
  map_smul' _ _ := Matrix.smul_mul _ _ _
  map_add' _ _ := Matrix.add_mul _ _ _

end right
end one_side
end NonUnitalNonAssocSemiring
end
