@[expose] public section

universe u

namespace OreLocalization

section Semiring

variable {R : Type*} [Semiring R] {S : Submonoid R} [OreSet S]

attribute [local instance] OreLocalization.oreEqv

variable {X : Type*} [AddCommMonoid X] [Module R X]

section UMP

variable {T : Type*} [Semiring T]

variable (f : R →+* T) (fS : S →* Units T)

variable (hf : ∀ s : S, f s = fS s)

theorem universalHom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ r : R, φ (numeratorHom r) = f r) :
    φ = universalHom f fS hf :=
  RingHom.toMonoidHom_injective <|
    universalMulHom_unique (RingHom.toMonoidHom f) fS hf (↑φ) huniv

end UMP
end Semiring
end OreLocalization
end
