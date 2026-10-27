public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Quasithin HeringK419 HeringK419U33

open Item419Res3

open scoped commutatorElement

open CFSG.Assembly.RankThreeEven (projSU)

namespace HeringK419U33

section Certs

theorem hasTwoWitness_yg : HasTwoWitness yg := by
  obtain ⟨i, hi, hne⟩ := y_moves
  refine ⟨Subgroup.closure CFSG.ASVolI.ChF.burnsideF4c_Qset,
    u33_syl.1.to_le CFSG.ASVolI.ChF.burnsideF4c_Qset_le_T,
    fun t ht => (Subgroup.mem_normalizer_iff.mp
      (CFSG.ASVolI.ChF.burnsideF4c_gen_norm 4 (by simp)) t).mp ht,
    u33Tel u33GenPG i, Subgroup.subset_closure ⟨i, hi, rfl⟩, fun h => hne ?_⟩
  have h1 : u33PresHom (yg * u33Tel u33GenPG i * yg⁻¹) = u33PresHom (u33Tel u33GenPG i) := by
    rw [h]
  rw [map_mul, map_mul, map_inv, u33Tel_hom, yg, u33PresHom_genPG] at h1
  have := congrArg (· * u33GenP 4) h1
  simpa [mul_assoc] using this

end Certs
end HeringK419U33
end CFSG.RankThree.PartTwo.Sec4
end
