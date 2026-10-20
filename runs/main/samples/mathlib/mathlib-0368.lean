@[expose] public section

open Set Filter

variable {ι : Type*}

variable (R : ι → Type*) (A : (i : ι) → Set (R i))

open Batteries.ExtendedBinder

scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]_[" f "]" =>
  RestrictedProduct r a f

scoped[RestrictedProduct]
notation3 "Πʳ " (...) ", " "[" r:(scoped R => R)", " a:(scoped A => A) "]" =>
  RestrictedProduct r a cofinite

namespace RestrictedProduct

open scoped RestrictedProduct

variable {𝓕 𝓖 : Filter ι}

section map

variable {ι₁ ι₂ : Type*}

variable (R₁ : ι₁ → Type*) (R₂ : ι₂ → Type*)

variable {𝓕₁ : Filter ι₁} {𝓕₂ : Filter ι₂}

variable {A₁ : (i : ι₁) → Set (R₁ i)} {A₂ : (i : ι₂) → Set (R₂ i)}

variable {S₁ : ι₁ → Type*} {S₂ : ι₂ → Type*}

variable [Π i, SetLike (S₁ i) (R₁ i)] [Π j, SetLike (S₂ j) (R₂ j)]

variable {B₁ : Π i, S₁ i} {B₂ : Π j, S₂ j}

variable (f : ι₂ → ι₁) (hf : Tendsto f 𝓕₂ 𝓕₁)

section set

@[simp]
lemma map_apply {G H : ι → Type*} {C : (i : ι) → Set (G i)}
    {D : (i : ι) → Set (H i)} (φ : (i : ι) → G i → H i)
    (hφ : ∀ᶠ i in 𝓕, MapsTo (φ i) (C i) (D i))
    (x : Πʳ i, [G i, C i]_[𝓕]) (j : ι) :
    x.map φ hφ j = φ j (x j) :=
  rfl

end set
end map
end RestrictedProduct
end
