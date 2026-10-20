namespace P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero

set_option autoImplicit false

namespace WeierstrassCurve

p2m_open

open MulAction

namespace VariableChange

p2m_open

variable {R : Type*} [CommRing R]

@[scoped simp] lemma ofUnit_s (u : Rˣ) : (ofUnit u).s = 0 := rfl

end VariableChange
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero
