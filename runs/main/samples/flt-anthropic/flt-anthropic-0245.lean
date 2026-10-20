namespace P2MW.S_Module_depth_quotient_eq_depth

open IsLocalRing RingTheory

namespace Ws14Port

variable (R S M : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

variable [AddCommGroup M] [Module R M] [Module S M] [Algebra R S] [IsScalarTower R S M]

variable [IsLocalHom (algebraMap R S)]

open IsLocalRing RingTheory Module RingTheory.Sequence

p2m_open

open scoped Pointwise

noncomputable section

p2m_reactivate

namespace IsLocalRing

p2m_open

variable (R : Type*) [CommRing R] [IsLocalRing R]

namespace IsCohenMacaulayOfDim

open IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma of_field (K : Type*) [Field K] : IsCohenMacaulayOfDim K 0 := by
  refine ⟨by rw [ringKrullDim_eq_zero_of_field K]; rfl, le_antisymm ?_ (by simp)⟩
  have h := Module.depth_le_dim K K
  rw [ringKrullDim_eq_zero_of_field K] at h
  exact_mod_cast h

end IsCohenMacaulayOfDim
end IsLocalRing
end
end Ws14Port
end P2MW.S_Module_depth_quotient_eq_depth
