@[expose] public section

universe uR uS uT uM uN uP uY

open CategoryTheory

namespace TopModuleCat

section Identity

variable {R : Type uR} [Ring R] [TopologicalSpace R]

/-- Restriction along the identity ring homomorphism is naturally isomorphic
to the identity functor. -/
noncomputable def restrictScalarsId :
    (restrictScalars (RingHom.id R) continuous_id : TopModuleCat.{uM} R ⥤ TopModuleCat.{uM} R) ≅
      𝟭 (TopModuleCat.{uM} R) :=
  NatIso.ofComponents restrictScalarsIdIso (by
    intro M N f
    ext x
    rfl)

end Identity
end TopModuleCat
end
