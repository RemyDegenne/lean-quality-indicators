namespace P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0

open scoped MatrixGroups ModularForm

open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

open scoped Pointwise

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

p2m_reactivate

p2m_reactivate

namespace W1pRR

open UpperHalfPlane Complex Function

open scoped ModularForm Real Manifold Topology

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Forms

variable [NeZero M']

def ι (u : (ZMod q)ˣ) : (ZMod (q * M'))ˣ :=
  Classical.choose (ZMod.unitsMap_surjective (dvd_mul_right q M') u)

end Forms
end W1pRR
end
end P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElem_eq_sum_exp_pow_smul_of_mem_Gamma0
