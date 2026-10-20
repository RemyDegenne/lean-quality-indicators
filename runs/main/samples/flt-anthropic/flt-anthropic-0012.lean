namespace P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq

set_option autoImplicit false

p2m_open

namespace WeierstrassCurve

p2m_open

section PointEquiv

variable {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K]
  (E : WeierstrassCurve F) (C : VariableChange F)

namespace VariableChange

p2m_open

lemma bc_negY (x y : K) :
    ((C • E)⁄K).negY ((C.baseChange K).ptX x) ((C.baseChange K).ptY x y) = (C.baseChange K).ptY x ((E⁄K).negY x y) := by
  rw [← baseChange_variableChange_smul]; exact negY_pt (C.baseChange K) (E⁄K) x y

end VariableChange
end PointEquiv
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
