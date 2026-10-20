public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped nonZeroDivisors NumberField IsMulCommutative

namespace TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

section ArtinHomAway

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

theorem artinElementAway_eq_artinElement {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    artinElementAway (L := L) hab S hur v = artinElement hab v.asIdeal (hur v hv) := by
  rw [artinElementAway, dite_eq_right hv]

end ArtinHomAway
end TauCeti.NumberFieldArithmetic
end
