@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

theorem stabilizer_quotient_one_mono {I J : Ideal R} (h : I ≤ J) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) ≤
      MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ J) := by
  intro u hu
  exact (J.mem_stabilizer_quotient_one u).mpr
    (h ((I.mem_stabilizer_quotient_one u).mp hu))

end Ideal
end
