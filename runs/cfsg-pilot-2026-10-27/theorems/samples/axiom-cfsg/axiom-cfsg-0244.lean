public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open

open CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

section ConjAutMul

variable {Γ : Type} [Group Γ]

theorem centerQuotAut_conjAut_mul_pow (L : Subgroup Γ) {g h : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ))
    (hh : h ∈ Subgroup.normalizer (L : Set Γ)) (hcomm : Commute g h) (k : ℕ) :
    centerQuotAut ↥L (conjAut L (g * h ^ k) (Subgroup.mul_mem _ hg (Subgroup.pow_mem _ hh k))) =
      centerQuotAut ↥L (conjAut L g hg) * (centerQuotAut ↥L (conjAut L h hh)) ^ k := by
  rw [← map_pow (centerQuotAut ↥L), conjAut_pow']
  rw [← map_mul]
  congr 1
  rw [conjAut_mul L hg (Subgroup.pow_mem _ hh k)]
  ext l
  rw [coe_conjAut, coe_conjAut]
  rw [show h ^ k * g = g * h ^ k from (hcomm.pow_right k).eq.symm]

end ConjAutMul
end CFSG.LocalAnalysis.GLTheoremA.CanonU3
end
