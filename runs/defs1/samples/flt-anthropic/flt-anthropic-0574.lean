namespace P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm

set_option autoImplicit false

open scoped MatrixGroups

section InlinedSAN123

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace ModularCurve

namespace PDPairing

namespace SanIDX

p2m_open

open CongruenceSubgroup Matrix.SpecialLinearGroup Matrix ModularCurve.Sanov ModularCurve.PDPairing.SanPM

open scoped MatrixGroups ModularGroup

section IndexGammaTwo

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

def upE (s : ℤ) : SL(2, ℤ) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

end IndexGammaTwo
end SanIDX
end PDPairing
end ModularCurve
end
end InlinedSAN123
end P2MW.S_ModularCurve_PDPairing_pairZFun_heckeT0_comm
