@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

/-- The finite-quotient description of homomorphisms between profinite
groups: `Hom(G, H) ≃ lim_V colim_U Hom(G/U, H/V)`.

The Hom limit–colimit description comes from Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §1, Exercise 3, using Mathlib’s finite-quotient limit. -/
noncomputable def homEquivHomLimit (G H : ProfiniteGrp.{u}) :
    (G ⟶ H) ≃ HomLimit G H where
  toFun := HomLimit.ofHom
  invFun := HomLimit.toHom
  left_inv := HomLimit.toHom_ofHom
  right_inv := HomLimit.ofHom_toHom

end ProfiniteGrp.FiniteQuotientHom
end
