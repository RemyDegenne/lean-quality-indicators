@[expose] public section

open Order

variable {ι : Sort*} {α β : Type*}

section Atomistic

variable (α) [PartialOrder α]

export IsAtomistic (isLUB_atoms)

export IsCoatomistic (isGLB_coatoms)

variable {α}

namespace CompleteAtomicBooleanAlgebra

/--
Representation theorem for complete atomic boolean algebras:
For a complete atomic Boolean algebra `α`, `toSetOfIsAtom` is an order isomorphism
between `α` and the set of subsets of its atoms.
-/
def toSetOfIsAtom {α} [CompleteAtomicBooleanAlgebra α] : α ≃o (Set {a : α // IsAtom a}) where
  toFun A := {a | a ≤ A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    have h : ∀ a ∈ Subtype.val '' S, IsAtom a := by
      rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    rw [← Subtype.val_injective.image_injective.eq_iff, eq_setOfPred_le_sSup_and_isAtom h]
    ext a
    simp
  map_rel_iff' {a b} := by
    simpa using le_iff_atom_le_imp.symm

end CompleteAtomicBooleanAlgebra
end Atomistic
end
