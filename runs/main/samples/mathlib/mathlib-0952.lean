@[expose] public section

open Fintype

open scoped BigOperators ComplexConjugate

scoped[ComplexOrder] attribute [instance 100] RCLike.toPartialOrder

attribute [instance 100] RCLike.toDecidableEq

variable {K E : Type*} [RCLike K]

namespace RCLike

variable (K)

variable {K} {z : K}

open OfScientific (ofScientific)

theorem isCauSeq_re (f : CauSeq K norm) : IsCauSeq abs fun n => re (f n) := fun _ ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa only [map_sub] using abs_re_le_norm (f j - f i)) (H _ ij)

end RCLike
end
