public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M) [Invertible (2 : R)]

/-- The linear map into the even Clifford algebra obtained by multiplying a generating vector on
the right by another generating vector. -/
def rightIotaEven (e : M) : M →ₗ[R] even Q :=
  (even.ι Q).bilin.flip e

end CliffordAlgebra
end
