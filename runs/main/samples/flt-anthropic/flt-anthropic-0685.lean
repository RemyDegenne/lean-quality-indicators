namespace P2MW.S_Module_depth_quotient_eq_depth

open IsLocalRing RingTheory

namespace Ws14Port

variable (R S M : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

variable [AddCommGroup M] [Module R M] [Module S M] [Algebra R S] [IsScalarTower R S M]

variable [IsLocalHom (algebraMap R S)]

open IsLocalRing RingTheory Module RingTheory.Sequence

noncomputable section

scoped instance instSubsingletonQuotientOfSubsingleton [Subsingleton M] (N : Submodule R M) : Subsingleton (M ⧸ N) :=
  Function.Surjective.subsingleton N.mkQ_surjective

lemma Module.depth_le_dim_annihilator
    [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ Module.annihilator R M) := by
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact Module.depth_le_krullDim_support _ _

end
end Ws14Port
end P2MW.S_Module_depth_quotient_eq_depth
