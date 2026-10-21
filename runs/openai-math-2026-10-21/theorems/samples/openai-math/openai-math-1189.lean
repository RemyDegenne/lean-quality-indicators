namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

universe u

variable {k : Type u} [Field k] [CharP k 2] (q : k)

local notation "T" => ArExplicit.T k q

variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

include hD

theorem tInducedDerived_shift_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 1)
    (f : (tInducedDerived q)⟦(1 : ℤ)⟧ ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  let e := TriangleRecurrence.shiftedMapEquiv (tInducedDerived q) (tSimpleDerived q)
    1 (n - 1) n (by omega)
  obtain ⟨g, rfl⟩ := e.surjective f
  rw [tInducedDerived_hom_zero q hq1 (n - 1) (by omega) g]
  simp [e, TriangleRecurrence.shiftedMapEquiv]

end ArExplicit.Resolution
end
end OAI
