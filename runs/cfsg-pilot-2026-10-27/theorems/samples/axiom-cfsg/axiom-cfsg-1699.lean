public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open Matrix Module CFSG.ComponentClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

section Semi

theorem semiMap_iterate_add (A : GL ι K) (σ : K ≃+* K) (k : ℕ) (v w : ι → K) :
    (ModelGen.semiMap A σ)^[k] (v + w) =
      (ModelGen.semiMap A σ)^[k] v + (ModelGen.semiMap A σ)^[k] w :=
  iterate_map_add (ModelGen.semiMap A σ) k v w

end Semi
end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
end
