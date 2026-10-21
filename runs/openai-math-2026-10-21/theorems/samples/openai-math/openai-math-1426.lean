namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

open SetRealization

universe u

variable {P : Type u} {s : Presentation P}

theorem realize_emptySet (D : Name.NameDomain s) (nonempty : D.names.Nonempty) (H : Set P) :
    Realize (D.values H) emptySet Fin.elim0 := by
  rw [emptySet, realize_ex]
  refine ⟨∅, D.empty_value_mem nonempty H, ?_⟩
  intro x _ member
  exact ZFSet.notMem_empty x member

end PartitionPilot.Forcing.SetFormula
end
end OAI
