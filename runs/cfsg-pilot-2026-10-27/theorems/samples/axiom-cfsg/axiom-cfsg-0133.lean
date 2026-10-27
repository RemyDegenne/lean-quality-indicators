public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Quasithin

open CFSG.Timmesfeld.Transvection

open scoped commutatorElement

variable {G : Type} [Group G]

theorem map_Rbar_subgroupOf {V H P K : Subgroup G} (hVK : V ≤ K) (hHK : H ≤ K)
    (hVH : V ≤ H) (hPK : P ≤ K) :
    (Rbar (V.subgroupOf K) (H.subgroupOf K) (P.subgroupOf K)).map
        (xbarEquivSubgroupOf hVK hHK hVH).toMonoidHom = Rbar V H P := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_Rbar_subgroupOf_iff hVK hHK hVH hPK z).1 hz
  · intro hy
    obtain ⟨z, rfl⟩ := (xbarEquivSubgroupOf hVK hHK hVH).surjective y
    exact ⟨z, (mem_Rbar_subgroupOf_iff hVK hHK hVH hPK z).2 hy, rfl⟩

end CFSG.RankThree.GF2n.Tim79a
end
