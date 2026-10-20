public section

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
  {F : Type*} [AddCommMonoid F] [TopologicalSpace F] [T2Space F]

section ClosedSubgroups

variable (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [TopologicalSpace M]
  [Module ℤ_[p] M] [ContinuousSMul ℤ_[p] M]

/-- The closed `ℤ_[p]`-submodule with the same carrier as a closed additive subgroup. -/
def ClosedAddSubgroup.toPadicIntSubmodule (H : ClosedAddSubgroup M) :
    ClosedSubmodule ℤ_[p] M where
  toSubmodule :=
    { H.toAddSubgroup with smul_mem' := fun c _ hx ↦ H.padicInt_smul_mem p hx c }
  isClosed' := H.isClosed'

end ClosedSubgroups
end
