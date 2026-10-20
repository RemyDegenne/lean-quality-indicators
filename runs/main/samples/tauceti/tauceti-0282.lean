public noncomputable section

open Module.Grassmannian TensorProduct

universe u

namespace TauCeti.HopfIdealChart

variable (R : Type u) [CommRing R] {H : Type u} [CommRing H] [HopfAlgebra R H]
  {k : ℕ} (x : Fin k → H)

variable {R x}

variable (R x)

variable {R x}

@[simp]
theorem homEquiv_symm_apply_mk {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) //
      ∃ I : Ideal (A ⊗[R] H), I.restrictScalars A = N.1.toSubmodule ∧ I.IsHopfIdeal A})
    (a : ChartAlgebra R x) :
    (homEquiv A).symm N (mk R x a) =
      (chartHomEquiv R x A).symm N.1 a :=
  (rfl)

end TauCeti.HopfIdealChart
end
