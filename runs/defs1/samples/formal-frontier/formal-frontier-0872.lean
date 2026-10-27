@[expose] public section

universe uι uκ uD

namespace KTheory

variable {ι : Type uι} (D : ι → Type uD) (κ : ι → Type uκ)

variable [∀ i, DivisionRing (D i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
  [∀ i, Nonempty (κ i)] [Finite ι]

namespace K0

/-- Integer coordinates of K₀ of a finite family of nonempty matrix rings
over division rings, using its existing additive group completion. -/
noncomputable def matrixFamilyEquiv :
    K0 (∀ i, Matrix (κ i) (κ i) (D i)) ≃+ (ι → ℤ) :=
  (piEquiv (fun i ↦ Matrix (κ i) (κ i) (D i))).trans
    (AddEquiv.piCongrRight fun i ↦
      (matrixEquiv (D i) (κ i)).symm.trans (finrankEquiv (D i)))

end K0
end KTheory
end
