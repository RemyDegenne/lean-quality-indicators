set_option warningAsError true

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.PullbackOpenImmersion

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

theorem awayMap_fst_bijective (f : R →+* T) (g : S →+* T)
    (b : f.pullback g) (hb : b ∈ RingHom.ker (f.pullbackSnd g)) :
    Function.Bijective (Localization.awayMap (f.pullbackFst g) b) := by
  have hb0 : b.1.2 = 0 := by
    have h := (RingHom.mem_ker).mp hb
    exact h
  have hbf : f b.1.1 = 0 := by
    calc
      f b.1.1 = g b.1.2 := b.2
      _ = 0 := by simp [hb0]
  constructor
  · apply (Localization.awayMap_injective_iff).2
    intro a ha
    refine ⟨1, ?_⟩
    have hmul : b * a = 0 := by
      apply Subtype.ext
      apply Prod.ext
      · change b.1.1 * a.1.1 = 0
        change a.1.1 = 0 at ha
        simp [ha]
      · change b.1.2 * a.1.2 = 0
        simp [hb0]
    simpa only [pow_one] using hmul
  · apply (Localization.awayMap_surjective_iff).2
    intro a
    let c : f.pullback g := ⟨(b.1.1 * a, 0), by simp [map_mul, hbf]⟩
    refine ⟨c, 1, ?_⟩
    change b.1.1 * a = b.1.1 ^ 1 * a
    rw [pow_one]

end AlgebraicGeometry.PullbackOpenImmersion
end
end
