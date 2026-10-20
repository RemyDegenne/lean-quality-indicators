@[expose] public section

universe uR uM uI

namespace LinearMap

variable {R : Type uR} [Semiring R]

variable {M : Type uM} [AddCommMonoid M] [Module R M]

variable {I : Type uI}

/-- The joint block selected by `ε`: true chooses the original range and false
chooses the original kernel at each index. -/
def jointBlock (p : I → Module.End R M) (ε : I → Bool) : Submodule R M :=
  ⨅ i, if ε i then (p i).range else (p i).ker

end LinearMap
end
