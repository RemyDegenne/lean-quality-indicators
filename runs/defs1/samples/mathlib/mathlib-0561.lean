@[expose] public section

open scoped MonoidAlgebra

universe w w' u u' v v'

namespace Representation

variable {k G V W X : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddCommGroup X] [Module k X]
  (ρ : Representation k G V) (τ : Representation k G W) (υ : Representation k G X)

section

open Coinvariants

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable abbrev quotientToCoinvariants :
    Representation k (G ⧸ S) (Coinvariants (ρ.comp S.subtype)) :=
  ofQuotient (toCoinvariants ρ S) S

end
end Representation
end
