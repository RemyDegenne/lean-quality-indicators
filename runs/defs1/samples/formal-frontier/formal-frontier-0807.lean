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

/-- Universal property for continuous homomorphisms to T1 targets which kill
all `n`-fold multiples. -/
def lift [T1Space B] (n : ℕ) (f : A →ₜ+ B)
    (hf : KillsMultiples n f) : TopologicalModN A n →ₜ+ B :=
  liftOfClosed n f (closedMultiples_le_ker n f hf)

end TopologicalModN
end
end
