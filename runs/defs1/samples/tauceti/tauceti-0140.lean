public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v v' w

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type} [Fintype κ]

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

/-- The Weyl representative `xᵢ(1) xⱼ(-1) xᵢ(1)` as a point of the Kostant toral closure.

The intended indices `i` and `j` are opposite roots in an `sl₂` pair. The definition itself only
uses their represented root subgroups; the `sl₂` relations enter when describing conjugation. -/
noncomputable def kostantToralWeylPoint (i j : I) (A : Type v) [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b wt A :=
  kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
      (Multiplicative.ofAdd (1 : A)) *
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt j A
      (Multiplicative.ofAdd (-1 : A)) *
    kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
      (Multiplicative.ofAdd (1 : A))

end TauCeti.UniversalEnvelopingAlgebra
end
