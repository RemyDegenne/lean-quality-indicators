public section

variable {G X : Type*} [Group G] [MulAction G X]

namespace MulAction

@[to_additive
  ]
theorem isPretransitive_iff_orbit_eq_univ (a : X) :
    IsPretransitive G X ↔ orbit G a = .univ := by
  rw [isPretransitive_iff_base a, Set.ext_iff]
  apply forall_congr'
  intro x
  simp_rw [Set.mem_univ, iff_true, mem_orbit_iff]

end MulAction
end
