public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.LinearAlgebra CFSG.Open Subgroup

open SemidirectProduct

variable {L : Type} [Group L] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : L →* LGL 2 W} {A : Subgroup L} {Z : Submodule (ZMod 2) W}

theorem w16l_mem_zHat_iff {x : VGL ρ} :
    x ∈ zHat ρ Z ↔ ∃ z ∈ Z, x = SemidirectProduct.inl (Multiplicative.ofAdd z) := by
  rw [zHat, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨Multiplicative.toAdd y, ?_, hxy.symm⟩
    rw [Multiplicative.mem_toSubgroup] at hy
    simpa using hy
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by rwa [Multiplicative.mem_toSubgroup], rfl⟩

end CFSG.LocalAnalysis.WeakClosure81
end
