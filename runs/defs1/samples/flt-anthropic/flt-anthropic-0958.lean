namespace P2MW.S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant

set_option autoImplicit false

p2m_open

open Topology

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace AutomorphicForm

p2m_open

namespace TKNHaar

variable (K : Type) [Field K] [NumberField K]

def ratCentralHom : Kˣ →* AdelicGL2 (𝓞 K) K :=
  (globalPoints (𝓞 K) K).comp (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom)

end TKNHaar
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
