public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L : Subgroup G}

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_transfer_i (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {S : Subgroup G}
    (h1 : ∀ y ∈ S, ∀ α : ℤˣ,
      ¬ InducesTypeSome L y 6 (-1) 1 α ∧ ¬ InducesTypeSome L y 6 (-1) 3 α) :
    ∀ q ∈ ffThetaImg (ffTheta6M hQ hdim hsgn e) S, ∀ α : ℤˣ,
      ¬ SimHasType q 1 α ∧ ¬ SimHasType q 3 α := by
  intro q hq α
  obtain ⟨s, hsN, hsS, hqs⟩ := mem_ffThetaImg_iff.mp hq
  have hind : InducesViaP L (Subgroup.center ↥L) hQ e s q := by
    have h := ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨s, hsN⟩
    rw [ffTheta6M] at hqs
    rwa [hqs] at h
  have key : ∀ r : ℕ, SimHasType q r α → InducesTypeSome L s 6 (-1) r α := by
    intro r hr
    exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, q, hdim, hsgn, hind, hr⟩
  exact ⟨fun hst => (h1 s hsS α).1 (key 1 hst), fun hst => (h1 s hsS α).2 (key 3 hst)⟩

end CFSG.OddStandard.SmallF3.Omega
end
