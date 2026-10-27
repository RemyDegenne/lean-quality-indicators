open scoped Finset

@[expose] public noncomputable section

open Complex UpperHalfPlane Matrix.SpecialLinearGroup

open scoped Topology Manifold MatrixGroups ComplexConjugate

namespace ModularForm

section GradedRing

/-- The `n`-th power of a modular form, as a modular form of weight `n * k`. -/
def pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k : ℤ} (f : ModularForm Γ k)
    (n : ℕ) : ModularForm Γ (n * k) :=
  n.rec (mcast (by simp) (1 : ModularForm Γ 0)) (fun n g ↦ (g.mul f).mcast (by grind))

end GradedRing
end ModularForm
end
