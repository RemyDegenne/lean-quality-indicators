public section

namespace DoubleCoset

variable {G : Type*} [Group G]

variable {G' : Type*} [Group G']

/-- Transport of a double-coset space along a group isomorphism `e : G ≃* G'`: the equivalence
`H \ G / K ≃ H' \ G' / K'` when `H'` and `K'` are the images of `H` and `K` under `e`. -/
def quotientCongr (H K : Subgroup G) {H' K' : Subgroup G'} (e : G ≃* G')
    (hH : H.map e = H') (hK : K.map e = K') :
    Quotient (H : Set G) K ≃ Quotient (H' : Set G') K' :=
  Quotient.congr e.toEquiv fun a b ↦ by
    subst hH hK
    rw [rel_iff, rel_iff]
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      exact ⟨e h, Subgroup.mem_map_of_mem _ hh, e k, Subgroup.mem_map_of_mem _ hk, by simp⟩
    · rintro ⟨h', hh', k', hk', hb⟩
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hk'
      exact ⟨h, hh, k, hk, e.injective (by simpa using hb)⟩

end DoubleCoset
end
