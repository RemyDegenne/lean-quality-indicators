@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable (K : Type u) (Γ : Type v)

variable [CommRing K] [Fintype Γ] [Group Γ]

/-- Comultiplication on functions, dual to multiplication in the group as
in Milne's *Algebraic Groups*, item 2.3. -/
noncomputable def comulAlgHom :
    FiniteGroupFunctions K Γ →ₐ[K]
      FiniteGroupFunctions K Γ ⊗[K] FiniteGroupFunctions K Γ :=
  (tensorAlgEquiv K Γ).symm.toAlgHom.comp <|
    AlgHom.pi fun p : Γ × Γ ↦ Pi.evalAlgHom K (fun _ : Γ ↦ K) (p.1 * p.2)

end FiniteGroupFunctions
end AlgebraicGeometry
end
