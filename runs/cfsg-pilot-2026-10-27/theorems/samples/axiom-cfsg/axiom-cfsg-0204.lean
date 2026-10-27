public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint

theorem exists_swap_of_mem_sphereDistThree
    {r t : NativeSporadic.B} {v u : CVert}
    (hv : clabelS v = babyToShat r) (hu : u ∈ sphereDistThree v) (ht : clabelS u = babyToShat t) :
    t ∈ Subgroup.centralizer ({r} : Set NativeSporadic.B) ∧
      ∀ K : Subgroup NativeSporadic.B, K.relIndex (Subgroup.centralizer {r}) = 2 → t ∉ K := by
  obtain ⟨hmem, hout, -⟩ := native_distance_three_label_is_outer_local_involution_final hu
  have htH : t ∈ Subgroup.centralizer ({r} : Set NativeSporadic.B) :=
    (mem_centralizer_iff_mem_vStab hv t).2 (by rw [← ht]; exact hmem)
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  refine ⟨htH, fun K hK => ?_⟩
  with_reducible_and_instances
    exact not_mem_of_relIndex_eq_two babyToShat (Subgroup.centralizer {r}) (vStab v)
      (mem_centralizer_iff_mem_vStab hv) (index_commutator_vStab hs) htH
      (fun y hy => hout y (hy.trans ht.symm)) hK

end CFSG.Monster.Existence
end
