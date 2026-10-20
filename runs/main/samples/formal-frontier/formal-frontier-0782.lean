@[expose] public section

namespace MvPolynomial

universe u v

variable (σ : Type u) (R : Type v) [CommRing R]

@[simp]
theorem idealOfVarsCotangentBasis_repr_X (i : σ) :
    (idealOfVarsCotangentBasis σ R).repr
      ((idealOfVars σ R).toCotangent
        ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩) =
      Finsupp.single i 1 := by
  rw [← idealOfVarsCotangentBasis_apply σ R i]
  exact (idealOfVarsCotangentBasis σ R).repr_self i

end MvPolynomial
end
