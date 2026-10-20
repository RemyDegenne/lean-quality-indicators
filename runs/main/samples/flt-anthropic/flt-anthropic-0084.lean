namespace P2MW.S_CuspForm_petersson_self_eq_zero_iff

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane Filter Topology

open scoped MatrixGroups ModularForm ComplexConjugate Modular

namespace AlliAux1Pet

variable {N : ℕ} {k : ℤ}

theorem tr_one (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : tr f 1 = ⇑f := by
  simp [tr]

end AlliAux1Pet
end
end P2MW.S_CuspForm_petersson_self_eq_zero_iff
