@[expose] public section

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

@[simp]
theorem baseChangeNormalFormHom_witness {p : ℕ} (hp : p.Prime) [CharP K p]
    (t : K) (α : L) (hα : α ^ p = algebraMap K L t) :
    baseChangeNormalFormHom K L hp t α hα (nilpotentWitness K L p t α) =
      thickenedLineW L p := by
  simp [nilpotentWitness, baseChangeNormalFormHom, Algebra.smul_def]

end
end FrobeniusTwistedLine
end
