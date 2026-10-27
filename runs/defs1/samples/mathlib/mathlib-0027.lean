@[expose] public section

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

scoped notation:9000 R "⟦X⟧" => PowerSeries R

section Algebra

variable {A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- Change of coefficients in power series, as an `AlgHom` -/
def mapAlgHom (φ : A →ₐ[R] B) :
    PowerSeries A →ₐ[R] PowerSeries B :=
  MvPowerSeries.mapAlgHom φ

end Algebra
end PowerSeries
end
end
