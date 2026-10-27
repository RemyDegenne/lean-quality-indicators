public section

open scoped Matrix

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {F : Type*} [Field F]

theorem mulVec_diag_apply {M : Matrix (Fin 3) (Fin 3) F} (hM : ∀ i j, i ≠ j → M i j = 0)
    (v : Fin 3 → F) (i : Fin 3) : (M *ᵥ v) i = M i i * v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hj
    rw [hM i j (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
end
