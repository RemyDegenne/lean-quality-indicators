public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace ModuleCat

open TauCeti

section Free

variable {k : Type w} [Ring k] (M : ModuleCat.{w} k) (X : TopCat.{w}) [ContractibleSpace X]

@[simp]
theorem finrank_singularHomology_of_contractibleSpace [Nontrivial k] (q : ℕ) :
    Module.finrank k (((singularHomologyFunctor (ModuleCat.{w} k) q).obj M).obj X) =
      if q = 0 then Module.finrank k M else 0 := by
  cases q with
  | zero =>
    rw [ite_eq_left rfl]
    let e := singularHomology₀SplitIso M (Classical.arbitrary X) ≪≫
      (isoZeroBiprod (isZero_reducedSingularHomologyFunctor_of_contractibleSpace M X 0)).symm
    exact e.toLinearEquiv.finrank_eq
  | succ q =>
    rw [ite_eq_right q.succ_ne_zero]
    have := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_singularHomologyFunctor_of_contractibleSpace M X q.succ_ne_zero)
    exact Module.finrank_zero_of_subsingleton

end Free
end ModuleCat
end
end
