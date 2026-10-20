namespace P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass

set_option autoImplicit false

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_FujisakiC2a

set_option autoImplicit false

p2m_open

open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Topology

open scoped NNReal Classical

noncomputable section

namespace M4aLocalCFT

namespace FujisakiC2a

variable {F : Type} [Field F] [NumberField F]

theorem archLog_integralUnitEmb (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    archLog (integralUnitEmb u) w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) := by
  rw [archLog_apply]
  congr 2
  exact norm_algebraMap_fst_apply (algebraMap (𝓞 F) F u) w

end FujisakiC2a
end M4aLocalCFT
end
end Fold_FujisakiC2a
end P2MW.S_NumberField_TateGlobal_compactSpace_normOneIdeleClass
