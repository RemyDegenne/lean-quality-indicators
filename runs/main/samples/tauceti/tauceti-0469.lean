public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w v'

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type}

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

section Fintype

variable [Fintype κ]

theorem kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : I} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (A : Type v) [CommRing A] (s : κ → Aˣ) (u : Multiplicative A) :
    kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s *
        kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A u *
        (kostantToralWeightTorusPoints e h ρ M hM hnil b wt A s)⁻¹ =
      kostantToralRootSubgroupPoints e h ρ M hM hnil b wt i A
        (Multiplicative.ofAdd
          ((torusCharacter s α : A) * Multiplicative.toAdd u)) := by
  have hmul := kostantTorusPoints_mul_kostantRootSubgroupPoints e h ρ M hM b wt hwt hα
    (hnil i) s ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
      (Multiplicative.ofAdd ((torusCharacter s α : A) * Multiplicative.toAdd u))) (by simp)
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom) hmul
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kostantToralWeightTorusPoints,
    coe_kostantToralRootSubgroupPoints]
  rw [mul_inv_eq_iff_eq_mul, ← basisMatrix_kostantTorusPoints M b wt (A := A) s]
  rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply, MonoidHom.comp_apply]
  simpa only [map_mul, MulEquiv.toMonoidHom_eq_coe] using hmatrix

end Fintype
end TauCeti.UniversalEnvelopingAlgebra
end
