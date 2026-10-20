namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_smul

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

p2m_open

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable (W : WeierstrassCurve A)

p2m_reactivate

open IsLocalRing

p2m_reactivate

p2m_reactivate

open IsLocalRing

p2m_reactivate

p2m_reactivate

open IsLocalRing

p2m_reactivate

namespace WeierstrassCurve

p2m_open

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Homomorphism

variable [DecidableEq L] [DecidableEq (ResidueField A)]

variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)

noncomputable def reduceHomVS :
    (W.map A.subtype).toAffine.Point →+ (W.map (residue A)).toAffine.Point where
  toFun := reducePointVS hΔ
  map_zero' := reducePointVS_zero hΔ
  map_add' := reducePointVS_add hΔ

end Homomorphism
end WeierstrassCurve
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_inZeroComponentAt_smul
