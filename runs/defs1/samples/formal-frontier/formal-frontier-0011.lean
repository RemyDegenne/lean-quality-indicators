@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The product of a dependent family of continuous additive equivalences. -/
noncomputable def continuousAddEquivPiCongrRight
    {ι : Type*} {A B : ι → Type*}
    [∀ i, Add (A i)] [∀ i, Add (B i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (F : ∀ i, A i ≃ₜ+ B i) : (∀ i, A i) ≃ₜ+ (∀ i, B i) :=
  ContinuousAddEquiv.mk (AddEquiv.piCongrRight fun i ↦ (F i).toAddEquiv)
    (Homeomorph.piCongrRight (fun i ↦ (F i).toHomeomorph)).continuous
    (Homeomorph.piCongrRight (fun i ↦ (F i).toHomeomorph)).symm.continuous

end ProfiniteGrp
end
