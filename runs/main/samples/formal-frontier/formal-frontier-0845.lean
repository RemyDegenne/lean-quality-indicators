@[expose] public section

noncomputable section

universe u v w

namespace KTheory.K0

variable (R : Type u) [CommRing R]

@[simp]
theorem determinantHom_pic_representative (ℓ : CommRing.Pic R) :
    determinantHom R (KTheory.K0.of R
      (CommRing.Pic.AsModule
        (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ))) =
      Additive.ofMul ℓ := by
  exact (determinantHom_of R
    (CommRing.Pic.AsModule
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ))).trans
        (congrArg Additive.ofMul (determinantLine_pic_representative R ℓ))

end KTheory.K0
end
end
