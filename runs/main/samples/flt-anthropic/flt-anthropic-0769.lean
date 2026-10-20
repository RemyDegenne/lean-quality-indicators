namespace P2MW.S_ModularCurve_jWidth_mul_ord_eq_ord_aeval_of_coe_eq_hasseRootFn_pow

attribute [-instance] ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

open AlgebraicCurve ModularCurve Polynomial

namespace HasseOrdBody

section OrdPoly

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_aeval_eq_zero [IsAlgClosed K] {J : F} (hJc : ∀ r : K, J - algebraMap K F r ≠ 0)
    {j₀ : K} (hj₀ : 1 ≤ v.ord (J - algebraMap K F j₀)) {Q : K[X]} (hQ : Q.Monic)
    (hev : Q.eval j₀ ≠ 0) : v.ord (aeval J Q) = 0 := by
  classical
  have hQroots : Q = (Q.roots.map fun r => X - C r).prod := by
    conv_lhs => rw [Splits.eq_prod_roots (IsAlgClosed.splits Q), hQ.leadingCoeff, map_one, one_mul]
  have haeval : aeval J Q = (Q.roots.map fun r => J - algebraMap K F r).prod := by
    conv_lhs => rw [hQroots]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro r _
    simp [Function.comp]
  have hfac_ne : ∀ g ∈ (Q.roots.map fun r => J - algebraMap K F r), g ≠ 0 := by
    intro g hg
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hg
    exact hJc r
  rw [haeval, ord_multiset_prod v _ hfac_ne, Multiset.map_map]
  refine Multiset.sum_eq_zero fun z hz => ?_
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
  have hrj : r ≠ j₀ := by
    rintro rfl
    exact hev (Polynomial.IsRoot.def.mp ((mem_roots hQ.ne_zero).mp hr))
  exact ord_sub_algebraMap_eq_zero v hJc hj₀ hrj

end OrdPoly
end HasseOrdBody
end P2MW.S_ModularCurve_jWidth_mul_ord_eq_ord_aeval_of_coe_eq_hasseRootFn_pow
