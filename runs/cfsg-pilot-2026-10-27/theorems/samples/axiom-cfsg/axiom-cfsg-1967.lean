public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Model

variable {H : Type*} [Group H] {V : Subgroup H} {Wm : Type*} [AddCommGroup Wm]
  [Module (ZMod 2) Wm]

theorem modelSub_iSup (θ : ↥V ≃* Multiplicative Wm) {ι : Sort*} (U : ι → Submodule (ZMod 2) Wm) :
    modelSub (H := H) θ (⨆ i, U i) = ⨆ i, modelSub θ (U i) := by
  unfold modelSub
  rw [OrderIso.map_iSup, Subgroup.map_iSup, Subgroup.map_iSup]

end Model
end CFSG.QuasithinUnique.Setup.Wreath
end
