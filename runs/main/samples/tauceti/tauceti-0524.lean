public section

namespace TauCeti

universe u v w x y

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section HeightLinearMap

variable [P.IsRootSystem]

theorem heightLinearMap_apply (b : P.Base) (m : M) :
    heightLinearMap P b m = (b.toWeightBasis.repr m).sum fun _ ↦ id := by
  rw [heightLinearMap, Module.Basis.coe_sumCoords]

end HeightLinearMap
end TauCeti
end
