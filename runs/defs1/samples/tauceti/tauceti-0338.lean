public section

open CategoryTheory CochainComplex.HomComplex

namespace TauCeti

namespace DGShiftClosure

universe v u

variable (R : Type v) [CommRing R] {V : Type u} [Category.{v} V] [Preadditive V] [Linear R V]

/-- The **normalized identification** `Hom(K, L)[s - r] ≅ Hom(K⟦r⟧, L⟦s⟧)` in degree `n`: a
morphism `K[r] ⟶ L[s]` of degree `n` in the shift closure, that is, a cochain `z` of degree
`n + (s - r)` from `K` to `L`, goes to the cochain from `K⟦r⟧` to `L⟦s⟧` with components
`(-1)^(r * n) • z^(i + r, j + s)`. -/
noncomputable def shiftCochainEquiv (X Y : DGShiftClosure (CochainComplex V ℤ)) (n : ℤ) :
    DGHom R n X Y ≃ₗ[R] DGHom R n (X.obj⟦X.shift⟧) (Y.obj⟦Y.shift⟧) :=
  (dgHomEquiv R X Y n).trans (cochainShiftLinearEquiv R X.obj Y.obj X.shift Y.shift n)

end DGShiftClosure
end TauCeti
end
