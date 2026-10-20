public section

open TensorProduct

namespace TauCeti

universe u v

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

variable (H : _root_.CommHopfAlgCat.{u} k)

theorem stabilizer_groupLike_isOpen {A : Type v} [Semiring A] [Bialgebra k A]
    (x : _root_.GroupLike (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup k) x :
      Set (Field.absoluteGaloisGroup k)) := by
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x.val)
    (H₂ := MulAction.stabilizer (Field.absoluteGaloisGroup k) x)
    ?_ (stabilizer_scalarExtension_isOpen x.val)
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  apply _root_.GroupLike.val_injective
  rw [val_smul]
  -- `val_smul` exposes the algebra equivalence underlying the opaque Galois wrapper.
  change (show AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k from σ) • x.val = x.val at hσ
  exact hσ

end CommHopfAlgCat
end TauCeti
end
