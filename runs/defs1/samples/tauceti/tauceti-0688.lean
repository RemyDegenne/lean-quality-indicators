public section

open CategoryTheory HomologicalComplex

namespace TauCeti

universe v u

namespace DGShiftClosure

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The action of the inclusion `X ↦ X[0]` on morphisms of degree `n`: a degree-`n` morphism
`X ⟶ Y` of `C` is a degree-`n` morphism `X[0] ⟶ Y[0]` of the shift closure. -/
noncomputable def ιHomEquiv (X Y : C) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (⟨X, 0⟩ : DGShiftClosure C) ⟨Y, 0⟩ :=
  ((dgHomComplex R X Y).XIsoOfEq (by rw [sub_self, add_zero])).toLinearEquiv.trans
    (dgHomEquiv R ⟨X, 0⟩ ⟨Y, 0⟩ n).symm

end DGShiftClosure
end TauCeti
end
