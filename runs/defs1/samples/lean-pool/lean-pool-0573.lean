@[expose] public section

namespace Homogenization

/-- Entry of a block matrix indexed by the doubled coordinate set. -/
def blockMatEntry {d : ℕ} (A : BlockMat d) : BlockCoord d → BlockCoord d → ℝ
  | Sum.inl i, Sum.inl j => A.upperLeft i j
  | Sum.inl i, Sum.inr j => A.upperRight i j
  | Sum.inr i, Sum.inl j => A.lowerLeft i j
  | Sum.inr i, Sum.inr j => A.lowerRight i j

end Homogenization
end
