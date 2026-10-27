public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

variable {X : Type} [Group X]

section Local

variable (e : ↥(elementaryGroup Q) →* X)

variable {e} {a : ↥(elementaryGroup Q)} {S T : Submodule F V}

section Layers

variable [Finite F] [FiniteDimensional F V]

theorem exists_smul_right_of_odd [Finite X] (hodd' : Odd (Nat.card F)) (D : LocalData e a S T)
    (layS : LayerGenOn Q S) (layT : LayerGenOn Q T) {N : Subgroup X}
    (hNle : N ≤ e.range ⊓ Subgroup.centralizer ({e a} : Set X))
    (hNnorm : ∀ x ∈ e.range ⊓ Subgroup.centralizer ({e a} : Set X), ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {g : ↥(elementaryGroup Q)} (hg : e g ∈ N)
    (h3 : 3 ≤ Module.finrank F T) : ∃ c : F, ∀ x ∈ T, (g : V ≃ₗ[F] V) x = c • x := by
  have h2 := two_ne_zero_of_odd_card hodd'
  exact exists_smul_of_commute_elemOn hodd' D.split.ndT h3
    (elementaryGroup_le_orthogonalGroup Q g.2) (preserves_of_odd h2 D hNle hodd hg).2
    (fun h hh => commute_join_of_odd h2 D layS layT hNle hNnorm hodd hg (Subgroup.mem_sup_right hh))

end Layers
end Local
end CFSG.ClassicalInvolution.ModelFacts.Orth15
end
