public section

open Polynomial NumberField

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

namespace NarrowClassGroup

theorem toClassGroup_injective_iff_exists_norm_eq_neg_one (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hd : 0 < d) :
    Function.Injective (toClassGroup (K := K)) ↔
      ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
  refine ⟨fun h => ?_, fun ⟨u, hu⟩ => toClassGroup_injective_of_norm_eq_neg_one hmin hgen hu⟩
  -- The narrow class of the principal ideal `(θ)` lies in the kernel, hence is trivial.
  have hker : mkPrincipal (Units.mk0 ((θ : K)) (coe_gen_ne_zero hmin)) = 1 :=
    h (by rw [toClassGroup_mkPrincipal, map_one])
  obtain ⟨v, hv⟩ := mkPrincipal_eq_one_iff.mp hker
  exact ⟨v, norm_eq_neg_one_of_isTotallyPositive_smul_gen hmin hgen hd (by simpa using hv)⟩

end NarrowClassGroup
end NumberField
end
