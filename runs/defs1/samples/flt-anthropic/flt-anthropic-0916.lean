namespace P2MW.S_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

noncomputable section

namespace P2MKcA

namespace M1728

variable {L : Type*} [Field L] [DecidableEq L]

section Count

variable [IsAlgClosed L]

variable (N : ℕ)

def cyc (T : {T : (W1 L).toAffine.Point // addOrderOf T = N}) : CycSub L N :=
  ⟨AddSubgroup.zmultiples T.1, ⟨⟨T.1, AddSubgroup.mem_zmultiples T.1⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, T.2]⟩

end Count
end M1728
end P2MKcA
end
end P2MW.S_ModularCurve_two_mul_natCard_moduliPoint_j_eq_1728_eq_dedekindPsi_add_nuTwo_of_ne_zero
