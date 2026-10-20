public section

namespace TauCeti

open CategoryTheory

section InvariantLineTrivial

variable (k : Type*) [Semiring k] (G X : Type*) [Group G] [MulAction G X] [Fintype X]
  [Nonempty X]

/-- For a nonempty index type, the invariant line is the trivial representation on the scalars.
The inverse sends a scalar to that multiple of the sum of the standard basis. -/
noncomputable def invariantLineEquivTrivial :
    (invariantLine k G X).toRepresentation.Equiv (Representation.trivial k G k) :=
  Representation.Equiv.mk
    { toFun := fun v => (v : MonoidAlgebra k X).coeff (Classical.arbitrary X)
      invFun := fun c => ⟨c • permutationSum k X, mem_invariantLine_iff.mpr ⟨c, rfl⟩⟩
      left_inv := fun v => by
        obtain ⟨c, hc⟩ := mem_invariantLine_iff.mp v.2
        apply Subtype.ext
        simp [← hc]
      right_inv := fun c => by simp
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp }
    fun g => by rw [toRepresentation_invariantLine]; rfl

end InvariantLineTrivial
end TauCeti
end
