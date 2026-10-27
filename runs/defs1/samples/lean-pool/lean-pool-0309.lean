@[expose] public section

universe u v

/-- Normalized signed correlation of a hypothesis on a finite sample. -/
noncomputable def rademacherCorrelation {X : Type u} {m : ℕ}
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X) : ℝ :=
  if _hm : m = 0 then 0
  else (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))

end
