set_option autoImplicit false

namespace ModularCurve.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section Prim

variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

variable [IsFreeGroup Φ]

noncomputable def sect (φ ψ : Additive Φ →+ R) : Φ →* CentralExt φ ψ :=
  IsFreeGroup.lift (fun a => (((0 : R), IsFreeGroup.of a) : CentralExt φ ψ))

end Prim
end ModularCurve.PDPairing
