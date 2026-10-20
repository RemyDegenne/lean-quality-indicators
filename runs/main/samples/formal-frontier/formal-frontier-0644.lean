@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ProfiniteGrp

@[simp] theorem residuePowerQuotientComponent_hom_one (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S)
    (hindex : (powerImage G hG n.val : Subgroup G).index = n.val) :
    (residuePowerQuotientComponent G hG g hg n hindex).hom
        (ULift.up (Multiplicative.ofAdd (1 : ZMod n.val))) =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := by
  rw [residuePowerQuotientComponent_hom_apply,
    powerImage_zmodContinuousMulEquiv_apply_one]

end ProfiniteGrp
end
