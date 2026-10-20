@[expose] public section

open commutatorElement Subgroup

section WithGroup

variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]

open Group

open QuotientGroup

namespace Group

@[to_additive]
theorem normalizerCondition_of_isNilpotent [h : IsNilpotent G] : NormalizerCondition G := by
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw [normalizerCondition_iff_only_full_group_self_normalizing]
  apply @nilpotent_center_quotient_ind _ G _ _ <;> clear! G
  · intro G _ _ H _
    exact @Subsingleton.elim _ Unique.instSubsingleton _ _
  · intro G _ _ ih H hH
    have hch : center G ≤ H := Subgroup.center_le_normalizer H |>.trans (le_of_eq hH)
    have hkh : (mk' (center G)).ker ≤ H := by simpa using hch
    have hsur : Function.Surjective (mk' (center G)) := Quot.mk_surjective
    let H' := H.map (mk' (center G))
    have hH' : normalizer H' = H' := by
      apply comap_injective hsur
      rw [comap_normalizer_eq_of_surjective _ hsur, comap_map_eq_self hkh]
      exact hH
    apply map_injective_of_ker_le (mk' (center G)) hkh le_top
    exact (ih H' hH').trans (symm (map_top_of_surjective _ hsur))

end Group
end WithGroup
end
