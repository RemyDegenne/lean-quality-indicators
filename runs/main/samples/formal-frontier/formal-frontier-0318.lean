@[expose] public section

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

@[simp]
theorem baseChangeNormalForm_tmul_x {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalForm K L hp t α hα ((1 : L) ⊗ₜ[K] x K p t) =
      thickenedLineX L p := by
  simp [baseChangeNormalForm]

end
end FrobeniusTwistedLine
end
