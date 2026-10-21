namespace OAI

section

open scoped BigOperators Topology Matrix.Norms.Operator

open MeasureTheory

open Filter MeasureTheory

open scoped BigOperators ENNReal Classical

open Filter

open scoped BigOperators Topology

open scoped BigOperators

namespace SharpTerminalLeave.PathForest

variable {s : ℕ} {α : Type*}

lemma mem_address_id (F : PathForest s) (i j : Fin s) :
    i ∈ F.address id j ↔ F.Ancestor i j := by
  induction j using (measure (fun j : Fin s => j.val)).wf.induction with
  | h j ih =>
    cases hp : F.parent j with
    | none =>
      rw [F.address_none id j hp,List.mem_singleton]
      constructor
      · rintro rfl
        exact Relation.ReflTransGen.refl
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨k,hk,_⟩
        · exact he
        · exact False.elim (by change F.parent j = some k at hk; rw [hp] at hk; cases hk)
    | some k =>
      rw [F.address_some id j k hp,List.mem_cons,ih k (F.property j k hp)]
      constructor
      · rintro (rfl | hik)
        · exact Relation.ReflTransGen.refl
        · exact hik.tail hp
      · intro h
        rcases F.ancestor_eq_or_predecessor h with he | ⟨l,hl,hil⟩
        · exact Or.inl he
        · have he := F.predecessor_unique hl hp
          subst l
          exact Or.inr hil

end SharpTerminalLeave.PathForest
end
end OAI
