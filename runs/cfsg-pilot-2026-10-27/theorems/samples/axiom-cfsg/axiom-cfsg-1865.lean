public section

namespace CFSG.QuasithinUnique.Setup.X3Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

theorem mem_invsC_iff (c : List ℕ) : c ∈ invsC ↔ c ∈ Core.autL ∧ Core.cmul c c = Core.cid ∧ c ≠ Core.cid := by
  unfold invsC isInvC
  simp [List.mem_filter, Bool.and_eq_true]

end CFSG.QuasithinUnique.Setup.X3Aut
end
