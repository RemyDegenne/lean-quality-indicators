public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

/-- The group scheme attached to the quotient Hopf algebra, representing
Milne's *Algebraic Groups*, item 2.5, over fields and more generally over
commutative bases of prime characteristic. -/
abbrev infinitesimalAdditiveGroupScheme : Grp (Over (Spec (.of K))) :=
  ⟨infinitesimalAdditiveUnderlyingScheme K p m⟩

end AlgebraicGeometry
end
end
