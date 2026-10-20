public section

namespace IsDedekindDomain

open IsDedekindDomain.HeightOneSpectrum

section Etale

variable {ι : Type*} (L : ι → Type*) [(i : ι) → Field (L i)]
  (B : (i : ι) → Type*) [(i : ι) → CommRing (B i)] [(i : ι) → IsDedekindDomain (B i)]
  [(i : ι) → Algebra (B i) (L i)] [(i : ι) → IsFractionRing (B i) (L i)]
  (S : (i : ι) → Set (HeightOneSpectrum (B i))) (n : ℕ)

variable {A : Type*} [CommRing A]

/-- The Selmer group of the etale algebra `A`, transported along a decomposition of `A` into a
product of fields. -/
noncomputable def selmerGroupOfEquiv
    (e : Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range ≃*
      ((i : ι) → (L i)ˣ ⧸ (powMonoidHom n : (L i)ˣ →* (L i)ˣ).range)) :
    Subgroup (Aˣ ⧸ (powMonoidHom n : Aˣ →* Aˣ).range) :=
  (selmerGroupPi L B S n).comap e.toMonoidHom

end Etale
end IsDedekindDomain
end
