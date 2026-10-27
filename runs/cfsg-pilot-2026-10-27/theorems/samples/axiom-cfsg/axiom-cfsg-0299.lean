public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.McLStd

theorem catalog_center_quotient_of_kProper {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) {K : Subgroup G} (hKtop : K ≠ ⊤)
    (hq : CFSG.IsQuasisimple ↥K) : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) := by
  set Z : Subgroup G := (center ↥K).map K.subtype with hZ
  have hZK : Z ≤ K := Subgroup.map_subtype_le _
  have hsub : Z.subgroupOf K = center ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hnormZ : (Z.subgroupOf K).Normal := by
    rw [hsub]
    infer_instance
  let e : ↥K ⧸ Z.subgroupOf K ≃* ↥K ⧸ center ↥K := QuotientGroup.quotientMulEquivOfEq hsub
  obtain ⟨-, hsimple, a, b, hab⟩ := hq
  have hsimple' : IsSimpleGroup (↥K ⧸ Z.subgroupOf K) := e.isSimpleGroup
  have hcat := hK K Z hKtop hZK hsimple'
    ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  exact CFSG.SectionRank.catalog_of_mulEquiv e.symm hcat

end CFSG.EvenSporadicStandard.Induction.Balance
end
