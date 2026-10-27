public section

open CategoryTheory

open TauCeti.SymmetricAlgebra

namespace AlgebraicGeometry.Proj

universe u v

variable (R : Type u) [CommRing R]

variable {M N P : Type u} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

variable {G : Type v} [Monoid G]

/-- A linear group action gives an action on `Proj(Sym M)` by scheme automorphisms.
Install this definition as a local instance to select the action. -/
@[instance_reducible]
noncomputable def symmetricAlgebraMulAction (ρ : G →* (M ≃ₗ[R] M)) :
    MulAction G (Proj (homogeneousSubmodule R M)) where
  smul g x := (symmetricAlgebraMapIso R (ρ g).symm).hom x
  one_smul x := by
    -- Expose the action field being constructed; its computation lemma is not yet available.
    change (symmetricAlgebraMapIso R (ρ 1).symm).hom x = x
    rw [map_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_symm,
      symmetricAlgebraMapIso_refl]
    rfl
  mul_smul g h x := by
    -- Expose the action field being constructed before using projective functoriality.
    change (symmetricAlgebraMapIso R (ρ (g * h)).symm).hom x =
      (symmetricAlgebraMapIso R (ρ g).symm).hom
        ((symmetricAlgebraMapIso R (ρ h).symm).hom x)
    rw [map_mul, LinearEquiv.mul_eq_trans, LinearEquiv.trans_symm]
    exact congrArg (fun e => e.hom x)
      (symmetricAlgebraMapIso_trans R (ρ g).symm (ρ h).symm)

end AlgebraicGeometry.Proj
end
