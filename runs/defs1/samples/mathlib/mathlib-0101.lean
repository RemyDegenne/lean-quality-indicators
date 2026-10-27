@[expose] public section

open scoped Finset

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.injective

end Place
end
