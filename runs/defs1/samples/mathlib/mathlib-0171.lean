@[expose] public section

noncomputable section

open FaithfulSMul Function Set

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

variable (i j)

variable {i j}

variable (h : LinearIndependent R ![P.root i, P.root j])

include h

omit h

include h

omit h

variable (i j)

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the index of the root
`β - q • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
def chainBotIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
      (le_refl <| P.chainBotCoeff i j) |>.choose
    else j

end RootPairing
end
end
