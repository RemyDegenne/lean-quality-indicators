@[expose] public section

noncomputable section

variable (R S P : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]

namespace MaximalSpectrum

variable {R S} (f : R →+* S) (g : S →+* P) (hf : Function.Bijective f) (hg : Function.Bijective g)

section Pi

variable {ι} (R : ι → Type*) [∀ i, CommSemiring (R i)] [∀ i, Nontrivial (R i)]

theorem toPiLocalization_not_surjective_of_infinite [Infinite ι] :
    ¬ Function.Surjective (toPiLocalization (Π i, R i)) := fun surj ↦ by
  classical
  have ⟨J, max, notMem⟩ := PrimeSpectrum.exists_maximal_notMem_range_sigmaToPi_of_infinite R
  obtain ⟨r, hr⟩ := surj (Function.update 0 ⟨J, max⟩ 1)
  have : r = 0 := funext fun i ↦ toPiLocalization_injective _ <| funext fun I ↦ by
    replace hr := congr($hr ⟨_, I.2.comap_piEvalRingHom⟩)
    dsimp only [toPiLocalization_apply_apply, Subtype.coe_mk] at hr
    simp_rw [toPiLocalization_apply_apply,
      ← Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply, hr]
    rw [Function.update_of_ne]; · simp_rw [Pi.zero_apply, map_zero]
    exact fun h ↦ notMem ⟨⟨i, I.1, I.2.isPrime⟩, PrimeSpectrum.ext congr($h.1)⟩
  replace hr := congr($hr ⟨J, max⟩)
  rw [this, map_zero, Function.update_self] at hr
  exact zero_ne_one hr

end Pi
end MaximalSpectrum
end
end
