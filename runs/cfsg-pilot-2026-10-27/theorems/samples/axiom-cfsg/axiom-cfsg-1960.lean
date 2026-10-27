public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Model

variable {H : Type*} [Group H] {V : Subgroup H} {Wm : Type*} [AddCommGroup Wm]
  [Module (ZMod 2) Wm]

theorem iSupIndep_modelSub (θ : ↥V ≃* Multiplicative Wm) {ι : Type*} {U : ι → Submodule (ZMod 2) Wm}
    (hU : iSupIndep U) : iSupIndep fun i => modelSub (H := H) θ (U i) := by
  have h1 : iSupIndep fun i => modelIso (U i) := (iSupIndep_map_orderIso_iff modelIso).2 hU
  have h2 := CFSG.LocalCores.iSupIndep_map_of_injective (f := θ.symm.toMonoidHom)
    θ.symm.injective h1
  exact CFSG.LocalCores.iSupIndep_map_of_injective (f := V.subtype) V.subtype_injective h2

end Model
end CFSG.QuasithinUnique.Setup.Wreath
end
