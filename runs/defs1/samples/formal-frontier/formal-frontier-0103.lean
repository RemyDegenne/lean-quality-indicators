set_option warningAsError true

@[expose] public section

open scoped Kronecker

universe u v w x

namespace Matrix

variable {R : Type u} [NonAssocSemiring R]

section Rectangular

variable {m : Type v} {n : Type w} {o : Type x} [DecidableEq o]

/-- Repeat a rectangular matrix on diagonal blocks indexed by `o`. -/
def repeatBlock (A : Matrix m n R) : Matrix (m × o) (n × o) R :=
  blockDiagonal (fun _ : o => A)

end Rectangular
end Matrix
end
