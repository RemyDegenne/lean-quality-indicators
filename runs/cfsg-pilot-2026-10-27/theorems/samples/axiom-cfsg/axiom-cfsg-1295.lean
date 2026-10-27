public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo

open scoped commutatorElement

namespace Wales154

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem innQ_normal (Y : Subgroup G) : (innQ Y).Normal := by
  refine ⟨fun τ hτ σ => ?_⟩
  obtain ⟨g, rfl⟩ := hτ
  exact ⟨σ g, (mul_conj_mul_inv_eq σ g).symm⟩

end Wales154
end CFSG.RankThree.PartTwo.Sec15
end
