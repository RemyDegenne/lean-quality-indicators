@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

@[simp]
theorem mem_stabilizer_quotient_one (I : Ideal R) (u : Rˣ) :
    u ∈ MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ↔
      (u : R) - 1 ∈ I := by
  rw [MulAction.mem_stabilizer_iff, Units.smul_def, ← Submodule.Quotient.mk_smul]
  simpa only [smul_eq_mul, mul_one] using (Submodule.Quotient.eq I :
    (Submodule.Quotient.mk (u : R) : R ⧸ I) = Submodule.Quotient.mk 1 ↔ _)

end Ideal
end
