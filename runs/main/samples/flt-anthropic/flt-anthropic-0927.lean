namespace P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

p2m_open

namespace ModularCurve

p2m_open

namespace ARails

open Complex

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

end ARails
end ModularCurve
end P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq
