set_option warningAsError true

@[expose] public section

open scoped Kronecker

universe u v w x

namespace Matrix

variable {R : Type u} [NonAssocSemiring R]

section Square

variable {m : Type v} {o : Type w}

variable [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

/-- Repeat a square matrix on diagonal blocks, as a ring homomorphism. -/
def repeatBlockHom : Matrix m m R →+* Matrix (m × o) (m × o) R :=
  (blockDiagonalRingHom (α := R) (m := m) (o := o)).comp
    (Pi.constRingHom o (Matrix m m R))

end Square
end Matrix
end
