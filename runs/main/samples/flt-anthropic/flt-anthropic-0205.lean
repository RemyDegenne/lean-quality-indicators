set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

namespace RealArchParam

theorem epsilonFactor_oddArtin : RealArchParam.oddArtin.epsilonFactor = I := by
  simp [RealArchParam.oddArtin, epsilonFactor]

end RealArchParam
end LanglandsTunnell
end
