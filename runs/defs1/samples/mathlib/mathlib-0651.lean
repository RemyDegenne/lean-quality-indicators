@[expose] public section

noncomputable section

open Function Set Submodule

open scoped Matrix

attribute [local simp] Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

variable [Finite ι] [IsDomain R] [CharZero R]

variable (b)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {b}

variable [DecidableEq ι]

variable [Fintype ι]

section ωConj

variable (N : LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R))

/-- The equivalence `x ↦ ωxω` as an operation on Lie submodules of the Geck construction. -/
def ωConjLieSubmodule :
    LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R) where
  __ := N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ ∈ N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

end ωConj
end RootPairing.GeckConstruction
end
end
