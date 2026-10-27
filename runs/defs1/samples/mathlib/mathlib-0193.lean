@[expose] public section

open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

section

variable {P' : Type*} [CommRing P'] [Algebra R P']

variable {P'' : Type*} [CommRing P''] [Algebra R P'']

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

variable (S P P')

variable [IsLocalization S P] [IsLocalization S P']

/-- `canonicalEquiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'`, which are both localizations of `R` at `S`. -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    { ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by rw [RingEquiv.toMonoidHom_refl', Submonoid.map_id]) with
      commutes' := fun _ => ringEquivOfRingEquiv_eq _ _ }

end
end FractionalIdeal
end
