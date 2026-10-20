set_option warningAsError true

@[expose] public section

noncomputable section

namespace GradedRing.Veronese

open scoped DirectSum

universe u v

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S]
  [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

@[simp] theorem zeroRingEquivAll_zeroCoefficient (j : ℕ) (a : 𝒮 (0 * j)) :
    zeroRingEquivAll 𝒮 0 (zeroCoefficient 𝒮 j a) =
      (⟨(a : S), by simpa only [zero_mul] using a.property⟩ : 𝒮 0) := by
  apply Subtype.ext
  simp only [zeroRingEquivAll_apply, zeroCoefficient, inclusion_of]

end GradedRing.Veronese
end
end
