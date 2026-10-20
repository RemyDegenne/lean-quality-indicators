public noncomputable section

open MvPolynomial

universe u v w z

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

theorem represents_zero_of_degree_lt {ν : MaxAddDegree R M} {x : R} {m : M}
    (h : ν x < (m : WithBot M)) : ν.Represents x m 0 :=
  ⟨h.le, (ν.homogeneousMk_eq_zero_iff m _).mpr h⟩

end MaxAddDegree
end
