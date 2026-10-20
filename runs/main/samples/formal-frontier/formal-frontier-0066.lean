set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalModN

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [IsTopologicalAddGroup C]

omit [IsTopologicalAddGroup B] in
theorem closedMultiples_le_ker [T1Space B] (n : ℕ) (f : A →ₜ+ B)
    (hf : KillsMultiples n f) : closedMultiples A n ≤ f.ker := by
  apply AddSubgroup.topologicalClosure_minimal
  · exact multiples_le_ker (A := A) (B := B) n f.toAddMonoidHom hf
  · exact isClosed_singleton.preimage f.continuous

end TopologicalModN
end
end
