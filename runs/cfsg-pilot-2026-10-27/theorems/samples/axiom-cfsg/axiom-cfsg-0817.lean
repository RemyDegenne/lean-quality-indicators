public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

section Ext

variable {ℓ f n m : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

variable (h : UnitaryFieldData ℓ f K)

theorem orthoEmb_resMat_mulVec_gu {x : Fin m → Fin n → K} (hx : ONExt.IsON σ₀ x)
    {s : primeFormUnitary h (idGram K n)} (hs : ∀ c, ∃ d, s • orthoEmb x c = orthoEmb x d)
    (c : Fin m → K) :
    orthoEmb x (ONExt.resMat σ₀ x ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c) =
      s • orthoEmb x c := by
  obtain ⟨d, hd⟩ := hs c
  rw [resMat_mulVec_eq_gu h hx hd, hd]

end Ext
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3
end
