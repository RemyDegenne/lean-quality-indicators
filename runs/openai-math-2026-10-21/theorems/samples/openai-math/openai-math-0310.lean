namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open scoped BigOperators

open MvPolynomial

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter

open scoped ENNReal NNReal BigOperators

noncomputable section

open scoped BigOperators

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

open scoped ComplexConjugate

noncomputable section

open scoped BigOperators

namespace CoordinateSweeps.PlacementOccurrence

open scoped Matrix.Norms.L2Operator

open Placement

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq I] in
theorem first_level_norm_le (ρ : UnitaryIrrep (Equiv.Perm Ω))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : I ↪ Ω)
    (hfixed : ∀ g : Equiv.Perm Ω, (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset Ω, A.card < Fintype.card I → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → Equiv.Perm Ω)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → (I ↪ Ω) → (I ↪ Ω) → ℝ)
    (hp : ∀ A x, DependsOn (fun y : I ↪ Ω => y) A (fun y => (p A x y : ℂ)))
    (hfull : (show Matrix (I ↪ Ω) (I ↪ Ω) ℂ from fun x y => (p Finset.univ x y : ℂ))=
      ∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a)) :
    ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤
      ‖alternatingKernel s p‖ := by
  let B : Matrix (Fin ρ.dimension) (I ↪ Ω) ℂ := synthesisMatrix ρ u x₀
  have hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : (I ↪ Ω) → ℂ,
      DependsOn (fun y : I ↪ Ω => y) A f → B.mulVec f=0 := by
    intro A hA f hf
    rw [synthesisMatrix_mulVec]
    exact synthesis_kills_proper_coordinates ρ.asRepresentation u x₀ hnof A hA f hf
  have hne : B ≠ 0 := synthesisMatrix_ne_zero ρ u hu x₀ (by
    intro σ hσ
    exact hfixed σ (fun i => congrArg (fun x : I ↪ Ω => x i) hσ))
  have hnorm : ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤ ‖alternatingKernel s p‖ := by
    apply ρ.norm_le_compression (actionMatrix (X := I ↪ Ω)) actionMatrix_unitary B hne
      (synthesisMatrix_covariant ρ u x₀)
    rw [alternatingKernel_mul_conjTranspose (fun y : I ↪ Ω => y) s hs p hp B hB,hfull,
      Matrix.sum_mul,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    exact ρ.adjoint_intertwines _ actionMatrix_unitary B (synthesisMatrix_covariant ρ u x₀) (g a)
  exact hnorm

end CoordinateSweeps.PlacementOccurrence
end
end
end
end
end
end
end
end
end OAI
