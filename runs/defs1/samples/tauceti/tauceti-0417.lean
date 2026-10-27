public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped nonZeroDivisors NumberField IsMulCommutative

namespace TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

section UnramifiedArtinHom

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (hur : ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The Artin map of an everywhere-unramified abelian extension.** This is the Artin map away
from the empty set, transported to the full group of invertible fractional ideals. -/
noncomputable def unramifiedArtinHom :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (L ≃ₐ[K] L) :=
  (artinHomAway (L := L) hab ∅ (fun v _ Q _ _ ↦ hur v Q)).comp
    (idealsAwayEmptyEquiv K).symm.toMonoidHom

end UnramifiedArtinHom
end TauCeti.NumberFieldArithmetic
end
