@[expose] public section

universe u v

open scoped Cardinal

namespace GroupLike

variable (R : Type u) (C : Type v)

variable [CommRing R] [IsDomain R] [AddCommGroup C] [Module R C] [Coalgebra R C]
  [Module.IsTorsionFree R C]

theorem setFinite_of_rank_lt_aleph0 (hrank : Module.rank R C < ℵ₀) :
    Set.Finite {c : C | IsGroupLikeElem R c} :=
  Set.finite_coe_iff.mp <|
    (valEquiv (R := R) (A := C)).finite_iff.mp (finite_of_rank_lt_aleph0 R C hrank)

end GroupLike
end
