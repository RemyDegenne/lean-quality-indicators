public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type*} {κ : Type*}

variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

attribute [local instance high] Algebra.toModule

section Param

variable (i : I)

variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

/-- The root subgroup map `x_α` with its parameter read in the value ring.

This is `kostantRootSubgroupPoints` reindexed along the identification `𝔾ₐ(A) ≃ A⁺` of
`AdditiveGroup.gaPointsMulEquiv`. The two forms carry the same information; this one states the
Chevalley relations in the shape downstream work uses, `xᵢ(t) xᵢ(u) = xᵢ(t + u)`. -/
noncomputable def kostantRootSubgroupParam (A : CommAlgCat.{w} ℤ) :
    Multiplicative A →* LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  (kostantRootSubgroupPoints e h ρ M hM i hnil).comp
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom

end Param
end TauCeti.UniversalEnvelopingAlgebra
end
