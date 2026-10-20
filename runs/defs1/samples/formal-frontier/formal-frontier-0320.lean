public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ)

variable (R : Type u) [CommRing R] [Algebra K R]

include K

/-- Postcomposition takes `p ^ m`-nilpotent points to `p ^ m`-nilpotent points. -/
@[expose] def infinitesimalAdditiveMap {S : Type u} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) :
    infinitesimalAdditiveSubgroup K p m R →+
      infinitesimalAdditiveSubgroup K p m S where
  toFun r := ⟨f r.val, by rw [mem_infinitesimalAdditiveSubgroup, ← map_pow, r.property, map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' r s := Subtype.ext (map_add f r.val s.val)

end AlgebraicGeometry
end
end
