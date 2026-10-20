public section

namespace TauCeti

open RootPairing

open Function Pointwise Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

section Combinatorics

variable [CharZero R] (b : P.Base)

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

variable [P.IsReduced]

variable [P.IsRootSystem]

theorem ncard_inversions_longestElement :
    (inversions P b (longestElement P b)).ncard = (posRoots P b).ncard := by
  rw [inversions_longestElement]

end Combinatorics
end TauCeti
end
