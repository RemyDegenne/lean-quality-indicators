@[expose] public section

section SourceQuantumUniformWitness

namespace QuantumQueryComplexity

open scoped Matrix

open Matrix

variable {X O : Type} [Fintype X] [DecidableEq O] {f : X → O}

section Realized

variable {R ι σ K X : Type} [Fintype R] [DecidableEq R] [Fintype ι]
  [DecidableEq ι] [Fintype σ] [DecidableEq σ] [Fintype K] [DecidableEq K]
  [Fintype X]

omit [DecidableEq R] [Fintype X] in
theorem qNormSq_realizedPacketU (u : X → ι → K → ℝ) (read : X → ι → σ)
    (x : X) :
    qNormSq (realizedPacketU (R := R) u read x)
      = 2 * ∑ p : ι × K, u x p.1 p.2 * u x p.1 p.2 := by
  classical
  have h := qInner_realizedPacketU_self (R := R) u read x
  rw [qInner_self] at h
  exact_mod_cast h

end Realized
end QuantumQueryComplexity
end SourceQuantumUniformWitness
end
