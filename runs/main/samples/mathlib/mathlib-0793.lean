@[expose] public section

open Set Filter TopologicalSpace Function Topology Filter

section IsTopologicalSemiring

variable (R : Type*)

variable {R}

variable [TopologicalSpace R]

section

variable [NonUnitalNonAssocRing R]

variable [IsSemitopologicalRing R]

theorem mulLeft_continuous (x : R) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_id.const_mul _

end
end IsTopologicalSemiring
end
