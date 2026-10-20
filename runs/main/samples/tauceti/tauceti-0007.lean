public section

namespace RootPairing

open Pointwise Set TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable (b : P.Base)

section PosRoots

variable [CharZero R] [IsDomain R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]

variable {x : M}

section Preorder

variable [Preorder R] [IsOrderedAddMonoid R]

theorem coroot'_nonpos_of_mem_negRoots (hx : x ∈ dominantChamber P b) {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i x ≤ 0 := by
  have h := coroot'_nonneg_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr hi)
  rw [RootPairing.coroot'_reflectionPerm_self] at h
  simpa using h

end Preorder
end PosRoots
end RootPairing
end
