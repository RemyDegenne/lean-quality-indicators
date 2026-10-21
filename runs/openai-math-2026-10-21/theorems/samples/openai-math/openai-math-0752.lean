namespace OAI

noncomputable section

namespace StronglyRationalVOA

universe u v

namespace LocalSkewFlow

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [CompleteSpace E]

section SkewFlowNorm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable (K : Module.End ℂ V)

lemma skewExp_smul (t : ℝ) (z : ℂ) (v : V) :
    skewExp K t (z • v) = z • skewExp K t v := by
  simp only [skewExp, skewExpTerm, map_smul, UniformSpace.Completion.coe_smul,
    smul_comm (_ / _) z, tsum_const_smul'']

end SkewFlowNorm
end LocalSkewFlow
end StronglyRationalVOA
end
end OAI
