public section

open CFSG.Open

open CFSG.Open

open scoped Pointwise

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem intersecting_local_primeCore_rank_obstruction
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) (hprime : prime.Prime)
    (sylow : Sylow prime ambient) {overgroup localGroup : Subgroup ambient}
    (hsylow : (sylow : Subgroup ambient) ≤ overgroup)
    (hcore : GLBWeakCore prime (sylow : Subgroup ambient) ≤ overgroup)
    (hrank : 3 ≤ pRank prime (localGroup ⊓ overgroup))
    (hescape : ¬ localGroup ≤ overgroup) :
    pRank prime (pCoreOf prime localGroup) ≤ 2 := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : (pCore prime localGroup).Normal := pCore_normal prime
  obtain ⟨localSylow, hcontained, _, _⟩ :=
    intersecting_local_has_contained_sylow prime hprime sylow hsylow hcore hrank
  have hcoreContained : pCoreOf prime localGroup ≤ overgroup :=
    (Subgroup.map_mono ((pCore_isPGroup prime).le_sylow_of_normal localSylow)).trans hcontained
  by_contra hlarge
  apply hescape
  exact normal_subgroup_sylow_rank_forces_containment prime hprime sylow
    hsylow hcore (pCore prime localGroup) hcoreContained
      (show 3 ≤ pRank prime (pCoreOf prime localGroup) by omega)

end CFSG.PreuniquenessRankFour.Helpers
end
