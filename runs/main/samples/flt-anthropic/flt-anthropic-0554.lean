namespace P2MW.S_WeierstrassCurve_exists_reduction_inZeroComponentAt

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

p2m_reactivate

p2m_open

p2m_reactivate

open IsLocalRing

p2m_reactivate

open IsLocalRing

p2m_reactivate

namespace WeierstrassCurve

p2m_open

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

theorem nonIntegralLocus_le_zeroComponentSubgroup :
    W.nonIntegralLocus ≤ W.zeroComponentSubgroup := fun _ hP =>
  W.hasNonsingularReduction_of_mem_nonIntegralLocus hP

end Carrier
end WeierstrassCurve
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_reduction_inZeroComponentAt
