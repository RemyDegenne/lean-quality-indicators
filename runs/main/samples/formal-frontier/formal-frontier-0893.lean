@[expose] public section

noncomputable section

universe u v w

namespace KTheory.K0

variable (R : Type u) [CommRing R]

theorem determinantHom_surjective : Function.Surjective (determinantHom R) := by
  intro ℓ
  exact ⟨KTheory.K0.of R
    (CommRing.Pic.AsModule
      (CommRing.Pic.mapRingHom (RingEquiv.toOpposite R).toRingHom ℓ.toMul)),
    determinantHom_pic_representative R ℓ.toMul⟩

end KTheory.K0
end
end
