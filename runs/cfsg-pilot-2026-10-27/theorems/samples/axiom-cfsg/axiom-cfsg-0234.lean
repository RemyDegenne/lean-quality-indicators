public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.FixWeylOne

open CFSG.Decide.F3

theorem exists_mem_allVecs (u : V 1) : ∃ l ∈ allVecs 4, toV l = u := by
  refine ⟨List.ofFn fun k : Fin (dim 1) => (u k).val, mem_allVecs.2 ⟨List.length_ofFn, ?_⟩, ?_⟩
  · intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
    exact ZMod.val_lt _
  · funext k
    simp [toV_apply, List.getD_eq_getElem?_getD]

end CFSG.StandardType.GGQ2Frame.ExcRaw.FixWeylOne
end
