@[expose] public section

open Equiv Equiv.Perm List

variable {α : Type*}

namespace Equiv.Perm

section Finite

variable [Finite α] [DecidableEq α]

theorem IsCycle.existsUnique_cycle_nontrivial_subtype {f : Perm α} (hf : IsCycle f) :
    ∃! s : { s : Cycle α // s.Nodup ∧ s.Nontrivial }, (s : Cycle α).formPerm s.prop.left = f := by
  obtain ⟨⟨s, hn⟩, hs, hs'⟩ := hf.existsUnique_cycle_subtype
  refine ⟨⟨s, hn, ?_⟩, ?_, ?_⟩
  · rw [hn.nontrivial_iff]
    subst f
    intro H
    refine hf.ne_one ?_
    simpa using Cycle.formPerm_subsingleton _ H
  · simpa using hs
  · rintro ⟨t, ht, ht'⟩ ht''
    simpa using hs' ⟨t, ht⟩ ht''

end Finite
end Equiv.Perm
end
