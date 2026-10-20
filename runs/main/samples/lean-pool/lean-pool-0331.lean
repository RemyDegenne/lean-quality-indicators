@[expose] public section

namespace QuantumAlg

namespace Gate

noncomputable section

variable {n : ℕ}

@[simp]
theorem one_apply (ψ : PureState n) : (1 : Gate n).apply ψ = ψ := by
  ext i
  change HilbertOperator.applyVec (1 : HilbertOperator n) (ψ : StateVector n) i = ψ i
  rw [HilbertOperator.one_applyVec]

end
end Gate
end QuantumAlg
end
