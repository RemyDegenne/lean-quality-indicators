public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.ARS CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem uForm_midExt (z w : Fin m → F) :
    uForm σ (midExt z : Fin (m + 2) → F) (midExt w) = uForm σ z w := by
  rw [uForm_eq, uForm_eq]
  refine (Fintype.sum_of_injective mid mid_injective (fun j => σ (z j) * w (Fin.rev j))
    (fun i => σ (midExt z i) * midExt w (Fin.rev i)) ?_ ?_).symm
  · intro i hi
    show σ (midExt z i) * midExt w (Fin.rev i) = 0
    rw [midExt_eq_zero_of_not_mem_range hi, map_zero, zero_mul]
  · intro j
    show σ (z j) * w (Fin.rev j) = σ (midExt z (mid j)) * midExt w (Fin.rev (mid j))
    rw [midExt_mid, rev_mid, midExt_mid]

end CFSG.Timmesfeld.Transvection.ModelRank
end
