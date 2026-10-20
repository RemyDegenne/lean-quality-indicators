public section

open CategoryTheory TensorProduct WithConv

open scoped commutatorElement

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {ι : Type*} {κ : Type*}

variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

attribute [local instance high] Algebra.toModule

variable [Fintype κ]

theorem kostantRootSubgroupParam_mem_kostantTorusSubsystemSubgroup {S : Set ι} {i : ι}
    (hiS : i ∈ S) (A : CommAlgCat.{w} ℤ) (t : Multiplicative A) :
    kostantRootSubgroupParam e h ρ M hM i (hnil i) A t ∈
      kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S A :=
  kostantSubsystemSubgroup_le_kostantTorusSubsystemSubgroup e h ρ M hM hnil b wt S A
    (kostantRootSubgroupParam_mem_kostantSubsystemSubgroup e h ρ M hM hnil hiS A t)

end TauCeti.UniversalEnvelopingAlgebra
end
