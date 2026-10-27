@[expose] public section

noncomputable section

open scoped Topology NNReal

variable {R : Type _} [CommRing R] (f : R → ℝ) {c : ℝ}

section seminormFromBounded

/-- The real-valued function sending `x ∈ R` to the supremum of  `f(x*y)/f(y)`, where `y` runs over
the elements of `R`. -/
def seminormFromBounded' : R → ℝ := fun x ↦ iSup fun y : R ↦ f (x * y) / f y

end seminormFromBounded
end
end
