@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Split a dependent additive product into the coordinates satisfying a
predicate and those satisfying its negation. -/
noncomputable def continuousAddEquivPiSubtypeProd
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, Add (F i)] [∀ i, TopologicalSpace (F i)] :
    (∀ i, F i) ≃ₜ+ (∀ i : {i // P i}, F i) × (∀ i : {i // ¬ P i}, F i) := by
  classical
  exact ContinuousAddEquiv.mk
    { toEquiv := Equiv.piEquivPiSubtypeProd P F
      map_add' := fun _ _ ↦ rfl }
    (Homeomorph.piEquivPiSubtypeProd P F).continuous
    (Homeomorph.piEquivPiSubtypeProd P F).symm.continuous

end ProfiniteGrp
end
