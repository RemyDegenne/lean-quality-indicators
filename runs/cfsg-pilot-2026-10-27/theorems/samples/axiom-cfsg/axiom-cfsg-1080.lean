public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup CFSG.Open

section Cent

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_K_mem_cent (h : DShape D t K) {k : D} (hk : k ∈ K) :
    k ∈ centralizer ({t} : Set D) := by
  rw [h.cent]
  exact Subgroup.mem_sup_right hk

end Cent
end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
end
