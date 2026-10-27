public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3

variable {F : Type} [Field F] [CharP F 2]

theorem mem_semilinear_of_map_V1 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ g ∈ (V1 : Subgroup (projectiveSL 3 F)), θ g ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    θ ∈ semilinearAutGroup 3 F := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hθ : θ ∈ standardAutGroup 3 F := by rw [hR]; exact Subgroup.mem_top θ
  rcases mem_or_mul_dualAut_mem hθ with h1 | h1
  · exact h1
  · exfalso
    have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
    have he : θ * iota =
        (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) := by
      rw [show (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) =
        θ * (dualAut 3 F * dualAut 3 F) * LinearFlag.conjAut 3 F W0 * dualAut 3 F by group,
        hδδ, mul_one]
      unfold iota
      group
    have he' : θ * iota ∈ semilinearAutGroup 3 F := by
      rw [he, htrans.2.2.2.2.1]
      exact mul_mem h1 (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    refine not_forall_V2_mem_V1 he' fun g hg => ?_
    rw [MulAut.mul_apply]
    exact h _ (iota_mem_V1 hg)

end L3T
end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
end
