namespace P2MW.S_CohCarrier_isEis_kernel_pair_of_prime

attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway

set_option autoImplicit false

open scoped MatrixGroups commutatorElement

open CongruenceSubgroup

namespace CohCarrier

namespace IsEisKernelPairPrime

p2m_open

universe u

section Bottom

p2m_open

theorem kernelPair_toGamma0 {N q : ℕ} [NeZero q] {A : Type*} [AddCommGroup A]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q) (g h : H1 N ⊤ A)
    (hgh : iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0)
    (γ : ↥(Gamma0 (N * q))) :
    toGamma0 g (Additive.ofMul (Ihara.ι₀ N q γ)) + toGamma0 h (Additive.ofMul (Ihara.ι₁ N q γ))
      = 0 := by
  have := DFunLike.congr_fun hgh (Additive.ofMul (eG (N * q) γ))
  rw [AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at this
  rw [toGamma0_apply, toGamma0_apply, ← iotaDeg_one_eG h₁, ← iotaDeg_q_eG hq]
  exact this

end Bottom
end IsEisKernelPairPrime
end CohCarrier
end P2MW.S_CohCarrier_isEis_kernel_pair_of_prime
