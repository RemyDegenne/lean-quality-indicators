public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped BigOperators ZeroObject

namespace CategoryTheory.AdditiveEuler

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {Γ : Type w} [AddCommGroup Γ]

variable (μ : C → Γ)

variable (hμ : ∀ S : ShortComplex C, S.ShortExact → μ S.X₂ = μ S.X₁ + μ S.X₃)

include hμ

omit hμ

variable (K : ChainComplex C ℤ) (i : ℤ)

include hμ

theorem local_decomposition :
    μ (K.X i) = μ (K.homology i) + μ (image (K.d (i + 1) i)) +
      μ (image (K.d i (i - 1))) := by
  have h₁ := hμ _ (cycles_image_shortExact K i)
  have h₂ := hμ _ (image_cycles_shortExact K i)
  change μ (K.X i) = μ (K.cycles i) + μ (image (K.d i (i - 1))) at h₁
  change μ (K.cycles i) = μ (image (K.d (i + 1) i)) + μ (K.homology i) at h₂
  rw [h₁, h₂]
  abel

end CategoryTheory.AdditiveEuler
end
end
