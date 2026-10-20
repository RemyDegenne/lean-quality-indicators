@[expose] public section

open Set

open scoped Graph

namespace Schoenflies

open Graph

variable {γ : Type*} {S₀ : CellStructure γ}
  {srcOuter srcDom tgtOuter tgtDom : Set Plane}

/-- Step 1 of direction (b), as the interface consumed by its relative-ear induction. -/
def TargetCommonSubdivision
    (P : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
    (H : Graph Plane γ) (Hdraw : γ → ℝ → Plane) : Prop :=
  ∃ (K : Graph Plane γ) (T₀ : GeneratedPair S₀ srcOuter srcDom tgtOuter tgtDom)
      (par₀ : γ → γ),
    K.IsTwoConnected ∧ K ≤ H ∧ IsTargetPartialTransferOf T₀ P K Hdraw par₀

end Schoenflies
end
