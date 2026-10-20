public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type} [Finite κ]

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (i : I)

variable (hnil : ∀ j, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

variable {r s : Fin n} {c : ℤ}

variable (hc : IsUnit c)

variable (hstep :
  ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V) = c • (b r : V))

variable (hsq : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : V)) = 0)

/-- The `i`th Kostant root subgroup as a closed subgroup scheme of the toral closure. Its
representing arrow is the factored root-subgroup morphism. -/
noncomputable def kostantRootSubgroupInToral :
    ClosedSubgroupScheme (kostantToralGroupScheme e h ρ M hM hnil b wt) :=
  haveI := isClosedImmersion_kostantRootSubgroupToToral
    e h ρ M hM i hnil b wt hc hstep hsq
  ClosedSubgroupScheme.mk (kostantRootSubgroupToToral e h ρ M hM hnil b wt i)

end TauCeti.UniversalEnvelopingAlgebra
end
