@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp

namespace IsProP

variable {p : ℕ} [Fact p.Prime] {G : ProfiniteGrp.{u}}

theorem of_continuousMulEquiv {H : ProfiniteGrp.{v}} (hG : IsProP p G)
    (e : G ≃ₜ* H) : IsProP p H where
  quotient_isPGroup U := by
    let V : OpenNormalSubgroup G :=
      { toSubgroup := U.toSubgroup.comap e.toMonoidHom
        isOpen' := U.isOpen'.preimage e.continuous_toFun }
    let q : (G ⧸ V.toSubgroup) →* (H ⧸ U.toSubgroup) :=
      QuotientGroup.map _ _ e.toMonoidHom fun _ hx ↦ hx
    apply (hG.quotient V).of_surjective q
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup z
    refine ⟨QuotientGroup.mk (e.symm y), ?_⟩
    change QuotientGroup.mk (e (e.symm y)) = QuotientGroup.mk y
    rw [e.apply_symm_apply]

end IsProP
end ProfiniteGrp
end
