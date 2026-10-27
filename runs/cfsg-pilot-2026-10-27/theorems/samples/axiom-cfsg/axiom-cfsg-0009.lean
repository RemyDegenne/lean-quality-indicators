public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected

open CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem hperp : L.K' ∉ KPerp Ω L.J := by
  intro hmem
  rcases hmem with h | h
  · have ht : IsUniqueInvolution L.J L.z' :=
      h ▸ ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hK'z'
    exact L.z'_ne_t
      (ht.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt))
  · obtain ⟨a, ha, hKa⟩ := tq_of_mem_omegaNbr C.hp C.hq C.hΩ.classical L.hJ.1 h
    have hat : a = L.t :=
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq ha).eq
        (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
    have htq : L.t ∈ trivialOnQuot L.K' :=
      (mem_trivialOnQuot_iff_actsTrivOnQuot (J := L.K')).mpr (hat ▸ hKa)
    have hq : CFSG.Open.IsQuasisimple ↥(modOdd z (exactCore z L.K')) := by
      rw [L.hK'img]
      exact isQuasisimple_map_of_ker_le_center _ (C.psi_ker C.i₁)
        (fundQuasisimple_core C.hp (C.D.isFundTag C.i₁) (C.D.admissible C.i₁)
          (C.four_le C.i₁ C.tag₁) L.R₂ L.hR₂)
    have hcen := oddQuotMk_centralizes_modOdd_exactCore L.hK'z' C.hc2 L.hK'.2 htq L.ht hq
    obtain ⟨r, hr, hrc⟩ := L.hd.not_central
    have hrm : C.psi C.i₁ r ∈ modOdd z (exactCore z L.K') := by
      rw [L.hK'img]
      exact ⟨r, hr, rfl⟩
    have h2 := hcen _ hrm
    rw [L.htbar] at h2
    apply hrc
    refine C.psi_ker C.i₁ (MonoidHom.mem_ker.mpr ?_)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact ChainFrame.commutator_eq_one_of_comm h2

end ChainLift
end Lift
end CFSG.ClassicalInvolution.Asc77
end
