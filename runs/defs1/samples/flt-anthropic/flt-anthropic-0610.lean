namespace P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_DenominatorClearing

namespace M4aLocalCFT

universe u

open AddSubgroup

variable {A B V : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

def nsmulHom (n : ℕ) : B →+ B where
  toFun b := n • b
  map_zero' := nsmul_zero n
  map_add' x y := nsmul_add x y n

end M4aLocalCFT
end Fold_DenominatorClearing
end P2MW.S_M4aHerbrand_sUnit_tateCard_mul_localDegreeProd
