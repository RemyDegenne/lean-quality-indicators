@[expose] public section

namespace Domain.Neighborhood.Theorem56Full

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

open Domain.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)

open Domain.Neighborhood.Exercise326 (cond)

open Domain.Neighborhood.Exercise511 (head tail push)

attribute [local implicit_reducible] PFun

section Rfind

variable (φf : ApproximableMap 𝒩 N)

theorem searchMap_step_next {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (hne : f (k ::ᵥ v) ≠ 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) =
      (searchMap φf).toElementMap (vecElem ((k + 1) ::ᵥ v)) := by
  obtain ⟨m, hm⟩ : ∃ m, f (k ::ᵥ v) = m + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hm, zeroMap_natElem_succ,
    Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]

end Rfind
end Domain.Neighborhood.Theorem56Full
end
