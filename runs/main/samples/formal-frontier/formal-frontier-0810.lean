@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

@[simp] theorem continuousMulEquivSupportedResidueLimit_generator
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (hg : IsTopologicalGenerator G g)
    (n : Nat.PowerIndex {p | hG.exponents p = ⊤}) :
    (continuousMulEquivSupportedResidueLimit G hG hfree g hg g).val n =
      ULift.up (Multiplicative.ofAdd (1 : ZMod n.val)) := by
  rw [continuousMulEquivSupportedResidueLimit_apply]
  change ULift.up
    ((powerImage_zmodContinuousMulEquiv G hG g hg n.val n.pos
      (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl) n)).symm
        (QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g)) = _
  exact congrArg ULift.up
    (powerImage_zmodContinuousMulEquiv_symm_apply_generator G hG g hg n.val n.pos
      (powerImage_index_eq_of_infiniteSupport G hG _ (Set.Subset.rfl) n))

end ProfiniteGrp
end
