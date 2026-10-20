@[expose] public section

open Polynomial

open scoped Polynomial

noncomputable section

variable {R : Type*}

section spectralNorm

section NontriviallyNormedField

open IntermediateField

universe u v

variable {K : Type u} [NontriviallyNormedField K] {L : Type v} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] [hu : IsUltrametricDist K]

set_option allowUnsafeReducibility true

section CompleteSpace

variable [CompleteSpace K]

namespace spectralNorm

variable (K L)

/-- `L` with the spectral norm is a `NontriviallyNormedField`. -/
@[instance_reducible]
def nontriviallyNormedField : NontriviallyNormedField L where
  __ := spectralNorm.normedField K L
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    ⟨algebraMap K L x, hx.trans_eq (spectralNorm_extends _).symm⟩

end spectralNorm
end CompleteSpace
end NontriviallyNormedField
end spectralNorm
end
end
