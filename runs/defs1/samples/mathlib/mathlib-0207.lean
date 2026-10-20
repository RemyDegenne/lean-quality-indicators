@[expose] public section

noncomputable section

open Set

open scoped ComplexConjugate

namespace Complex

variable {z : ℂ}

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ (‖·‖)) : CauSeq ℝ abs :=
  ⟨_, isCauSeq_re f⟩

end Complex
end
end
