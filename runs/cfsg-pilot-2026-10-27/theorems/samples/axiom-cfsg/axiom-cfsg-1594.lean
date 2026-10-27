public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Polynomial Module CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial

open CFSG.RankThree.PartOne.KCPrimary

open CFSG.RankThree.PartOne.KCUnitary (blockGL blockApply unitaryCentralizer
  mem_unitaryCentralizer supportedUnitary supportedUnitary_le_unitaryCentralizer root_ne_zero
  finrank_adjoinRoot)

open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Fixed

variable {B : LinearMap.BilinForm K V}

variable [FiniteDimensional K V] {x : LinearMap.GeneralLinearGroup K V}

omit [FiniteDimensional K V] in
theorem altTransvection_mem_unitaryCentralizer (H : AltPrimaryData B x) {v : V}
    (hv : (x : Module.End K V) v = v) : altTransvection H.alt v ∈ unitaryCentralizer B x := by
  rw [mem_unitaryCentralizer]
  refine ⟨mem_sesqUnitaryGroup.mpr fun u w => ?_, ?_⟩
  · simp only [altTransvection_apply, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, H.alt v, H.skew u v]
    ring
  · refine LinearMap.ext fun u => ?_
    simp only [Module.End.mul_apply, altTransvection_apply, map_add, map_smul, hv]
    congr 2
    have := H.isom_apply v u
    rwa [hv] at this

end Fixed
end CFSG.ComponentClassification.RankTwoClassical
end
