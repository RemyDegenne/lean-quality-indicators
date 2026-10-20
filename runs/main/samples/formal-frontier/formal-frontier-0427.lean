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

section CompactHausdorff

variable [CompactSpace A] [T2Space A]

@[simp]
theorem compactModNEquiv_mk (n : ℕ) (a : A) :
    compactModNEquiv (A := A) n (mkQ n a) = ModN.mkQ n a := by
  unfold compactModNEquiv
  dsimp only
  change compactToModN (A := A) n (mkQ n a) = _
  rw [compactToModN_mk]
  rfl

end CompactHausdorff
end TopologicalModN
end
end
