public section

namespace TauCeti.AdditiveCode

variable {A ι κ μ : Type*} [AddGroup A]

/-- The coordinate permutations preserving an additive code. Their action on words is
`x ↦ x ∘ e.symm`. -/
def permutationAut (C : AddSubgroup (ι → A)) : Subgroup (Equiv.Perm ι) where
  carrier := {e | reindex C e.symm = C}
  one_mem' := by simp [Equiv.Perm.one_def]
  mul_mem' := by
    intro e f he hf
    have h : reindex (reindex C f.symm) e.symm = C := by rw [hf, he]
    rw [reindex_reindex] at h
    simpa [Equiv.Perm.mul_def] using h
  inv_mem' := by
    intro e he
    have h : reindex C e = C := by
      calc
        reindex C e = reindex (reindex C e.symm) e := by rw [he]
        _ = C := reindex_reindex_symm C e.symm
    simpa [Equiv.Perm.inv_def] using h

end TauCeti.AdditiveCode
end
