public section

open CategoryTheory

open scoped MonoidAlgebra

universe u v

namespace Representation

open TauCeti TauCeti.Representation

section OrbitIndex

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {V : Type u} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)

variable [FiniteDimensional k V]

/-- **The inertia cosets index the isotypic components in Clifford's theorem.** A component is
sent to the coset of any `g` whose translated constituent cuts out that component, and generic
orbit--stabilizer identifies this with the left cosets of the constituent's inertia group. -/
noncomputable def isotypicComponentsEquivQuotientInertia [ρ.IsIrreducible]
    (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ) :
    isotypicComponents k[N] (_root_.Representation.asModule (ρ.comp N.subtype)) ≃
      G ⧸ inertia (FDRep.of σ.toRepresentation) :=
  (componentsEquivOrbit ρ hσ).trans
    (MulAction.orbitEquivQuotientStabilizer G
      (toSkeleton (FDRep.of σ.toRepresentation))) |>.trans
    (Subgroup.quotientEquivOfEq (stabilizer_toSkeleton_fdRepOf_eq_inertia ρ σ))

end OrbitIndex
end Representation
end
