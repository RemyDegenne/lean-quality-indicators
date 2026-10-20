@[expose] public section

open Set Function

variable {ι α β : Type*} {l : Filter α}

open Filter

theorem Nat.cofinite_eq_atTop : @cofinite ℕ = atTop := by
  refine le_antisymm ?_ atTop_le_cofinite
  refine atTop_basis.ge_iff.2 fun N _ => ?_
  simpa only [mem_cofinite, compl_Ici] using! finite_lt_nat N

end
