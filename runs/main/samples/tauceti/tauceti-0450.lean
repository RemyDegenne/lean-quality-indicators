public section

open Polynomial

namespace Finset

variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R]

variable {F F' B B' : Finset R[X]} {f b b' : R[X]}

@[gcongr]
theorem mcCallumProjection_mono (hF : F ⊆ F') (hB : B ⊆ B') :
    F.mcCallumProjection B ⊆ F'.mcCallumProjection B' := by
  intro a ha
  rw [mem_mcCallumProjection] at ha ⊢
  rcases ha with ⟨f, hf, rfl⟩ | ⟨b, hb, i, hi, rfl⟩ | ⟨b, hb, rfl⟩ |
    ⟨b, hb, b', hb', hne, rfl⟩
  · exact .inl ⟨f, hF hf, rfl⟩
  · exact .inr <| .inl ⟨b, hB hb, i, hi, rfl⟩
  · exact .inr <| .inr <| .inl ⟨b, hB hb, rfl⟩
  · exact .inr <| .inr <| .inr ⟨b, hB hb, b', hB hb', hne, rfl⟩

end Finset
end
