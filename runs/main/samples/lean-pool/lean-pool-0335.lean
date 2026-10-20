@[expose] public section

open Nat

open Fin Finset

variable {n m s : ℕ}

lemma chainTup_induction_compl :
    {natAdd n 0, natAdd n 2}ᶜ = insert (natAdd n 1) (univ.map (castAddEmb 3)) := by
  ext i
  simp_rw [mem_compl, mem_insert, mem_singleton, mem_map, mem_univ, true_and, coe_castAddEmb]
  cases i using addCases <;> grind

end
