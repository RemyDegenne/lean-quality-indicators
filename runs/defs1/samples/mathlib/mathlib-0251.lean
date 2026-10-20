@[expose] public section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

variable {A : Type*}

namespace PositiveLinearMap

section PreGNS

variable [NonUnitalRing A] [PartialOrder A] [Module ℂ A] (f : A →ₚ[ℂ] ℂ)

variable [StarRing A] [StarOrderedRing A] [SelfAdjointDecompose A] [StarModule ℂ A]
    [IsScalarTower ℂ A A] (f : A →ₚ[ℂ] ℂ)

/--
The (semi-)inner product space whose elements are the elements of `A`, but which has an
inner product-induced norm that is different from the norm on `A` and which is induced by `f`.
-/
noncomputable abbrev preGNSpreInnerProdSpace : PreInnerProductSpace.Core ℂ f.PreGNS where
  inner a b := f (star (f.ofPreGNS a) * f.ofPreGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

end PreGNS
end PositiveLinearMap
end
