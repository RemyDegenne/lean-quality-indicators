public section

open AlgebraicGeometry CategoryTheory TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type} [Finite κ]

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

/-- The torus-subsystem carrier as a closed subgroup scheme of the full toral closure. -/
noncomputable def kostantTorusSubsystemToToral
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (S : Set I) :
    kostantTorusSubsystemGroupScheme e h ρ M hM b wt S (fun i => hnil i.1) ⟶
      kostantToralGroupScheme e h ρ M hM hnil b wt :=
  CommHopfAlgCat.quotientSpecMapOfLe (GeneralLinear.coordinateHopfAlgebra ℤ n)
    (kostantToralDefiningIdeal_le_kostantTorusSubsystemDefiningIdeal
      e h ρ M hM b wt hnil S)

end TauCeti.UniversalEnvelopingAlgebra
end
