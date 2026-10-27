namespace P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero

set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup

open scoped MatrixGroups

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace IharaSolH25

namespace Dock

open CongruenceSubgroup IharaSolH25.Q2Step

open scoped MatrixGroups

variable (N q : ℕ)

noncomputable def cqEquiv (hq : 0 < q) : ↥(GUp N q) ≃* ↥(GLow N q) :=
  { cqHom N q with
    invFun := fun γ => ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩
    left_inv := fun δ => by
      apply Subtype.ext; apply Subtype.ext
      show upMat N q (cqHom N q δ) = _
      exact conjLowerMat_cqMat N q hq δ (dvd_c_of_GLow N q (cqHom N q δ))
    right_inv := fun γ => by
      apply Subtype.ext; apply Subtype.ext
      show cqMat N q ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩ = _
      exact conjUpperMat_upMat N q hq γ
        (dvd_b_of_GUp N q ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩) }

end Dock
end IharaSolH25
end P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero
