public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo

open CFSG Matrix

open CFSG.LocalAnalysis.ComponentInitial

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem hf_mulVec_left (X : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) :
    hf h (X *ᵥ u) v = hf h u (adj h X *ᵥ v) := by
  rw [hf_mulVec, adj_adj]

end CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo
end
