@[expose] public section

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} [DecidableEq α] {β : Type v}

namespace Equiv.Perm

theorem signAux_mul {n : ℕ} (f g : Perm (Fin n)) : signAux (f * g) = signAux f * signAux g := by
  rw [← signAux_inv g]
  unfold signAux
  rw [← prod_mul_distrib]
  refine prod_nbij (signBijAux g) signBijAux_mem signBijAux_injOn signBijAux_surj ?_
  rintro ⟨a, b⟩ hab
  dsimp only [signBijAux]
  rw [mul_apply, mul_apply]
  rw [mem_finPairsLT] at hab
  by_cases hg : g b < g a
  · simp [*]
  obtain hf | hf := (f.injective.ne <| g.injective.ne hab.ne).lt_or_gt <;>
    simp_all [le_of_lt, not_le_of_gt, not_lt_of_ge]

end Equiv.Perm
end
