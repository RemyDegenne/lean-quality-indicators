public section

open Polynomial

open scoped IntermediateField

namespace TauCeti.GenusDrop

variable (p : ℕ) [hp : Fact p.Prime]

theorem constantCompositum_eq_top (h2 : p ≠ 2) :
    constantCompositum (curveField p) (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p))) = ⊤ := by
  set C := constantCompositum (curveField p) (RatFunc (ZMod p)) (RatFunc (RatFunc (ZMod p)))
  have hs : sElement p ∈ C := algebraMap_mem_constantCompositum _ _ _ RatFunc.X
  have hy : genY p ∈ C := IntermediateField.algebraMap_mem C (genY' p)
  have hx : genX p ∈ C := by
    rw [← algebraMap_ratFuncAlgebraOfTranscendental_X (transcendental_genX p),
      IsScalarTower.algebraMap_apply (RatFunc (constants p)) (curveField p)]
    exact IntermediateField.algebraMap_mem C _
  have hX : (RatFunc.X : RatFunc (RatFunc (ZMod p))) ∈ C := by
    rw [X_eq_genY_div p h2]
    exact div_mem hy (pow_mem (sub_mem hx hs) _)
  refine eq_top_iff.mpr fun z _ ↦ ?_
  have hle : (RatFunc (ZMod p))⟮(RatFunc.X : RatFunc (RatFunc (ZMod p)))⟯.toSubfield ≤
      C.toSubfield := by
    rw [IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr (Set.union_subset ?_ (by simpa using hX))
    rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_constantCompositum _ _ _ c
  exact hle (by rw [RatFunc.adjoin_X, IntermediateField.top_toSubfield]; exact Subfield.mem_top z)

end TauCeti.GenusDrop
end
