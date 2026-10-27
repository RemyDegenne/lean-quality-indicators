set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors TensorProduct

section BC

variable {K : Type*} [Field K] {k : Type*} [Field k] [Algebra K k] {V : Type*} [AddCommGroup V]
  [Module K V] [Module.Finite K V]

theorem finrank_range_le_bc (f : V →ₗ[K] V) :
    Module.finrank K (LinearMap.range f) ≤
      Module.finrank k (LinearMap.range (f.baseChange k)) := by
  classical
  let c := Module.finBasis K (LinearMap.range f)
  have hli : LinearIndependent K (fun j => ((c j : LinearMap.range f) : V)) :=
    c.linearIndependent.map' (LinearMap.range f).subtype (by simp)
  have h2 := linearIndependent_bcVec (k := k) hli
  have hmem : ∀ j, bcVec (K := K) k ((c j : LinearMap.range f) : V) ∈
      LinearMap.range (f.baseChange k) := by
    intro j
    obtain ⟨x, hx⟩ := (c j).2
    refine ⟨bcVec k x, ?_⟩
    show (f.baseChange k) ((1 : k) ⊗ₜ[K] x) = (1 : k) ⊗ₜ[K] ((c j : LinearMap.range f) : V)
    rw [LinearMap.baseChange_tmul, hx]
  have h3 : LinearIndependent k (fun j => (⟨_, hmem j⟩ : LinearMap.range (f.baseChange k))) :=
    LinearIndependent.of_comp (LinearMap.range (f.baseChange k)).subtype h2
  have : Module.Finite k (k ⊗[K] V) := Module.Finite.of_basis (Algebra.TensorProduct.basis k (Module.finBasis K V))
  simpa using h3.fintype_card_le_finrank

end BC
end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
end
