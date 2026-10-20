set_option autoImplicit false

open Function

open scoped TensorProduct

universe u v w

namespace Deformation

namespace WittGroup

variable (R : Type u) [CommRing R] (p : ℕ) (n : ℕ) (J : Type v)

variable {R p n J}

variable [hp : Fact p.Prime]

variable (R p n J)

variable {R p n J}

variable (R p n J)

variable {R p n J}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

theorem pointsEquiv_eq_map_univ (φ : Coord R p n J →ₐ[R] A) (j : J) :
    pointsEquiv φ j = TruncWitt.map (p := p) φ.toRingHom (univ R p n j) := (map_univ φ.toRingHom j).symm

end Points
end WittGroup
end Deformation
