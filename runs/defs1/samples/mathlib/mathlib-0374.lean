open scoped Finset

@[expose] public section

variable {G H ι ι' : Type*} [Group G] [Group H]

namespace Group

namespace Generators

variable (P : Generators G ι)

/-- The transport of a generating family along a surjective homomorphism. -/
protected def map (f : G →* H) (hf : Function.Surjective f) : Generators H ι where
  val := f ∘ P.val
  closure_eq_top := by
    rw [Set.range_comp, ← MonoidHom.map_closure, P.closure_eq_top,
      Subgroup.map_top_of_surjective f hf]

end Generators
end Group
end
