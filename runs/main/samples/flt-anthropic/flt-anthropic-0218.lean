namespace P2MW.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant

set_option autoImplicit false

p2m_open

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm

p2m_open

namespace ZKNHaar

variable (K : Type) [Field K] [NumberField K]

theorem continuous_sheet (a : Kˣ) : Continuous (sheet K a) :=
  (continuous_const.mul continuous_subtype_val).subtype_mk _

end ZKNHaar
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
