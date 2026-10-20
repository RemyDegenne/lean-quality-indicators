@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower

open Stage5AboveTwoLower.S5ARepair

open Stage5AboveTwoLower.S5AFinalRepair

open Stage5AboveTwoLower.S5AGlobalC2

open Stage5AboveTwoLowerResume

lemma hasFDerivAt_repairSelectedValue {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) {chi : ℝ} (hchi : 0 < chi)
    (ell : Point d → ℝ) (hconv : O3.IsConvexObjective ell)
    (hlip : IsOneLipschitz p ell) (x : Point d) :
    HasFDerivAt (repairSelectedOracle p d chi ell).value
      (pairingCLM ((repairSelectedOracle p d chi ell).gradient x)) x := by
  apply hasFDerivAt_of_global_support_and_lp_lipschitz
    (by linarith : 1 < p) (div_nonneg (repairMpd_nonneg hp hd) hchi.le)
  · exact fun a b ↦ repairSelectedGradient_support hp hd hchi ell hconv hlip a b
  · exact fun a b ↦ repairSelectedGradient_lipschitz hp hd hchi ell hconv hlip a b

end V7.Stage5AboveTwoLowerS5A2Envelope
end
