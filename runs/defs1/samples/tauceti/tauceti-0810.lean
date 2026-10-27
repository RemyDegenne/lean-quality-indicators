public section

open TensorProduct

namespace TauCeti

universe u v

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

/-- Bridge the tautological action across the opaque `Field.absoluteGaloisGroup` definition. -/
noncomputable abbrev instMulSemiringActionAlgebraicClosure :
    MulSemiringAction (Field.absoluteGaloisGroup k) (AlgebraicClosure k) := by
  unfold Field.absoluteGaloisGroup
  exact AlgEquiv.applyMulSemiringAction

end CommHopfAlgCat
end TauCeti
end
