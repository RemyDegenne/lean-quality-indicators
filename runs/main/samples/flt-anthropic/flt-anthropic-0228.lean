namespace P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000

p2m_open

open scoped NNReal

scoped instance (F : Type) [Field F] [NumberField F] :
    LocallyCompactSpace (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ :=
  inferInstance

p2m_reactivate

section Fold_ArchLocalGlobalModulus

set_option autoImplicit false

p2m_open

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField

namespace TateGlobal

p2m_open

variable {F : Type} [Field F] [NumberField F]

section LGArch

variable (w : InfinitePlace F)

p2m_reactivate

theorem archCentralUnit_val_mul_fst_self (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w = (a : w.Completion) * x.1 w := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * x.1 w = _
  rw [archCentralUnit_fst_self]

end LGArch
end TateGlobal
end NumberField
end
end Fold_ArchLocalGlobalModulus
end P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
