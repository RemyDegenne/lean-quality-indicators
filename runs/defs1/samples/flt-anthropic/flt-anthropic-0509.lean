set_option autoImplicit false

@[simps! +simpRhs]
def AddAut.mulLeft' {R : Type*} [Semiring R] : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut' _ _
