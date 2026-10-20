@[expose] public section

namespace Matrix

variable {ι l m n p R S}

/-- All the matrix entries, arranged into one column. -/
@[simp]
def vec (A : Matrix m n R) : n × m → R :=
  fun ij => A ij.2 ij.1

end Matrix
end
