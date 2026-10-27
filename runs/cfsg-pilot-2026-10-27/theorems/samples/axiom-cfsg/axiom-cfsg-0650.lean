public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier

open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover

variable {n : ℕ}

theorem wordG_mem {K : Subgroup (Equiv.Perm (Fin n))} (gg : ℤ → Equiv.Perm (Fin n))
    {w : List ℤ} (h : ∀ z ∈ w, gg z ∈ K) : wordG gg w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons z w ih =>
    rw [wordG, List.map_cons, List.prod_cons]
    exact K.mul_mem (h z List.mem_cons_self) (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

end CFSG.EvenSporadicStandard.TwoRu.HypOne
end
