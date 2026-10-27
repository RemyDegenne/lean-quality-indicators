@[expose] public section

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

/-- The left coset of `H` obtained by multiplying by the nonzero scalar `alpha`. -/
noncomputable def scaledLeftCoset
    (alpha : E) (halpha : alpha ≠ 0) (H : Subgroup Eˣ) : Finset Eˣ := by
  classical
  exact Finset.univ.image fun h : H ↦ scalarUnit alpha halpha * (h : Eˣ)

end BGS.Markoff
end
