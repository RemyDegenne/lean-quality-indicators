public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Recognition.McLMultiplier CFSG.CosetTable

section Words

variable {G : Type*} [Group G]

theorem lift_mk_cons (g : Fin 6 → G) (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (l :: w)) =
      (if l.2 then g l.1 else (g l.1)⁻¹) * FreeGroup.lift g (FreeGroup.mk w) := by
  have e : FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w := rfl
  rw [e, map_mul, lift_mk_single]

end Words
end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
end
