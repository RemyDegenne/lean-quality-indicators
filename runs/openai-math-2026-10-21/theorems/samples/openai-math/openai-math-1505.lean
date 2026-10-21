namespace OAI

section

namespace Erdos3

open MeasureTheory

open scoped BigOperators

theorem blockCubeWeight_coordinate_fderiv {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (a : BlockParameter B F α → ℝ) (b : B) (f : F) (r : Option α) :
    fderiv ℝ (blockCubeWeight w) a (Pi.single (b, f, r) 1) =
      fderiv ℝ w ((blockCubeFlatten B F α).symm a) (Pi.single (b, f) (Pi.single r 1)) := by
  have hd := (hw.differentiable one_ne_zero ((blockCubeFlatten B F α).symm a)).hasFDerivAt.comp a
    (blockCubeFlatten B F α).symm.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (w ∘ (blockCubeFlatten B F α).symm) a (Pi.single (b, f, r) 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ w ((blockCubeFlatten B F α).symm a)) (blockCubeFlatten_symm_single b f r)

end Erdos3
end
end OAI
