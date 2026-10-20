@[expose] public section

variable {l m n o p q : Type*} {m' n' p' : o → Type*}

variable {R : Type*} {α : Type*} {β : Type*}

open Matrix

namespace Matrix

section BlockDiag

section

variable (o m n α)

/-- `Matrix.blockDiag` as an `AddMonoidHom`. -/
@[simps]
def blockDiagAddMonoidHom [AddZeroClass α] : Matrix (m × o) (n × o) α →+ o → Matrix m n α where
  toFun := blockDiag
  map_zero' := blockDiag_zero
  map_add' := blockDiag_add

end
end BlockDiag
end Matrix
end
