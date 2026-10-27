public section

open CFSG.Open

open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace Involution

open SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem pRank_map_conj (K : Subgroup G) (x : G) :
    CFSG.Open.pRank 2 (K.map (MulAut.conj x).toMonoidHom) = CFSG.Open.pRank 2 K := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two (MulAut.conj x⁻¹).toMonoidHom
      (MulAut.conj x⁻¹).injective (K.map (MulAut.conj x).toMonoidHom)
    have hK : (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = K := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id K
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply, inv_inv]
      group
    rwa [hK] at h
  · exact CFSG.SectionRank.pRank_le_map one_lt_two _ (MulAut.conj x).injective K

end Involution
end CFSG.ComponentClassification.AschbacherTheorem5
end
