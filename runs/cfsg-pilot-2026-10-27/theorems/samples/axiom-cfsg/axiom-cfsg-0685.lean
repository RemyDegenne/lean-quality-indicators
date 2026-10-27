public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits

theorem ggStdPos_conj_mem_ggTorus_of_actsAs {K : Type*} [Group K] {D : UniversalRootDatum K}
    {h m : K} {w : (coxeterMatrix D.isFiniteType).Group} (hh : h ∈ ggTorus D)
    (hm : ActsAs D m w) : m * h * m⁻¹ ∈ ggTorus D := by
  refine Subgroup.mem_iInf.mpr fun δ => Subgroup.mem_iInf.mpr fun hδ => ?_
  have hδ' : weylAction D.isFiniteType w⁻¹ δ ∈ D.roots := weylAction_mem_roots _ _ hδ
  have hN : h ∈ Subgroup.normalizer (D.rootGroup (weylAction D.isFiniteType w⁻¹ δ) : Set K) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh _) hδ'
  rw [mem_normalizer_iff_map_conj, mul_assoc, map_conj_mul, map_conj_mul, hm.inv δ hδ,
    mem_normalizer_iff_map_conj.mp hN, hm _ hδ', weylAction_apply_inv_apply]

end CFSG.StandardType
end
