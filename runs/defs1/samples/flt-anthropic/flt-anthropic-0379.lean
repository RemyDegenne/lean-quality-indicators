namespace P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section

open PowerSeries

universe u v

namespace P2M

namespace TadicPS

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

variable (e : A →ₐ[R] R)

def IsPointDerivation (D : A →ₗ[R] R) : Prop :=
  ∀ a b : A, D (a * b) = e a * D b + e b * D a

end TadicPS
end P2M
end P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section
