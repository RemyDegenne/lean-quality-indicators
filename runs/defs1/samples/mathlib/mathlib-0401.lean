@[expose] public section

open Set

attribute [local ext] Matroid

namespace Matroid

variable {α : Type*} {M : Matroid α}

macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := {terminal := true})
  (rule_sets := [$(Lean.mkIdent `Matroid):ident]))

section copy

/-- create a copy of `M : Matroid α` with independence and base predicates and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
@[simps] def copy (M : Matroid α) (E : Set α) (IsBase Indep : Set α → Prop) (hE : E = M.E)
    (hB : ∀ B, IsBase B ↔ M.IsBase B) (hI : ∀ I, Indep I ↔ M.Indep I) : Matroid α where
  E := E
  IsBase := IsBase
  Indep := Indep
  indep_iff' _ := by simp_rw [hI, hB, M.indep_iff]
  exists_isBase := by
    simp_rw [hB]
    exact M.exists_isBase
  isBase_exchange := by
    simp_rw [show IsBase = M.IsBase from funext (by simp [hB])]
    exact M.isBase_exchange
  maximality := by
    simp_rw [hE, show Indep = M.Indep from funext (by simp [hI])]
    exact M.maximality
  subset_ground := by
    simp_rw [hE, hB]
    exact M.subset_ground

end copy
end Matroid
end
