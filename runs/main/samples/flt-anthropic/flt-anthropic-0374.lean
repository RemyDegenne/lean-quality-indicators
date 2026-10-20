namespace P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow

set_option autoImplicit false

universe u

p2m_open

namespace WeierstrassCurve

namespace NodalCubic

p2m_open

theorem tpow2 (j : ℕ) : tpow (2 * j + 2) = ts := if_pos ⟨j + 1, by ring⟩

end NodalCubic
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_Phi_nodalCubic_eq_X_pow
