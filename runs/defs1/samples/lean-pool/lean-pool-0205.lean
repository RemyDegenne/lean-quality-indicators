@[expose] public section

open Set Function

open CategoryTheory CategoryTheory.SingleObj Quiver

open unitInterval

noncomputable section

universe u

namespace FiniteGraphFreeGroup

/-- A continuous parametrisation of the part of an interval cell from `t` to
    its source endpoint. -/
def graphEdgeRetraction (t : I) : C(I, I) where
  toFun s :=
    ⟨(1 - (s : ℝ)) * (t : ℝ),
      unitInterval.mul_mem
        ⟨unitInterval.one_minus_nonneg s, unitInterval.one_minus_le_one s⟩ t.2⟩
  continuous_toFun := by fun_prop

end FiniteGraphFreeGroup
end
end
