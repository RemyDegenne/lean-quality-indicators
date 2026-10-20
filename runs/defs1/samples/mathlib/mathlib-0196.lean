@[expose] public section

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

section Defs

/-- Interpret an `AddMonoidAlgebra` as a homogeneous `DirectSum`. -/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  f.coeff.toDFinsupp

end Defs
end
