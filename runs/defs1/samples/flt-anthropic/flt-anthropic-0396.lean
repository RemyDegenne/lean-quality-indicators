namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option synthInstance.maxHeartbeats 800000

noncomputable section

p2m_reactivate

p2m_open

open scoped Classical nonZeroDivisors NNReal ENNReal

namespace NumberField

namespace AdelicFourier

namespace Ws25

p2m_open

variable (F : Type) [Field F] [NumberField F]

section Split

def split : (AdeleRing (𝓞 F) F) ≃ₜ+ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F :=
  ContinuousAddEquiv.mk' ((eHomeo F).prodCongr (Homeomorph.refl _)) fun x y => by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F (x + y).1, (x + y).2)
        : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F)
      = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)
        + (InfiniteAdeleRing.ringEquiv_mixedSpace F y.1, y.2)
    rw [Prod.mk_add_mk, ← map_add]
    rfl

end Split
end Ws25
end AdelicFourier
end NumberField
end
end P2MW.S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
