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

@[simp]
theorem map_mk (n : ℕ) (f : A →ₜ+ B) (a : A) :
    map n f (mkQ n a) = mkQ n (f a) := rfl

end TopologicalModN
end
end
