@[expose] public section

noncomputable section

namespace UnitriangularStageCoordinateRing

variable (K : Type) [CommRing K] (n r : ℕ)

theorem survivingInclusion_injective : Function.Injective (survivingInclusion n r) :=
  Subtype.val_injective

end UnitriangularStageCoordinateRing
end
end
