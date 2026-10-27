public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)

include hP in
theorem normalizerAction_mem_sylowQuotient
    {x : Subgroup.normalizer (J : Set (EscapingQuotient z))}
    (hxS : (x : EscapingQuotient z) ∈ escapingSylowImage S z) {y : J ⧸ Subgroup.center J}
    (hy : y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J))) :
    componentNormalizerAction J x y ∈ (P.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center J)) : Subgroup (J ⧸ Subgroup.center J)) := by
  rw [Sylow.coe_mapSurjective] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  rw [componentNormalizerAction_mk]
  refine Subgroup.mem_map_of_mem _ ?_
  have hpS : (p : EscapingQuotient z) ∈ escapingSylowImage S z ⊓ J :=
    hP ▸ Subgroup.mem_map_of_mem J.subtype hp
  have hxp : ((J.normalizerMonoidHom x p : J) : EscapingQuotient z) ∈
      escapingSylowImage S z ⊓ J := by
    refine ⟨?_, (J.normalizerMonoidHom x p).2⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem hxS hpS.1)
      ((escapingSylowImage S z).inv_mem hxS)
  rw [← hP] at hxp
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hxp
  rwa [show J.normalizerMonoidHom x p = q from Subtype.ext hqe.symm]

end RankOneSetting
end CFSG.ProperTwoGeneratedCore.Lemma37
end
