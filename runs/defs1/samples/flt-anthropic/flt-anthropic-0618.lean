namespace P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one

set_option autoImplicit false

p2m_reactivate

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

noncomputable section

p2m_reactivate

p2m_reactivate

namespace CSTower

variable {a b : ℚ}

local notation "𝔾" => (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ

local notation "U" => Submodule.finiteIdeleStabilizer

local notation "conj" => Submodule.conjByFiniteIdele

def degVForget (R : Submodule ℤ ℍ[ℚ, a, b]) (s : 𝔾) (v : ClassSet (U (meetOrder R s))) : ℕ+ :=
  Nat.toPNat' ((unitGroup (conj (meetOrder R s) v.out)).relIndex (unitGroup (conj R v.out)))

end CSTower
end
end P2MW.S_CerednikDrinfeld_exists_finiteHom_classSetDegeneracyData_meetOrder_forget_and_shift_degTotal_eq_add_one
