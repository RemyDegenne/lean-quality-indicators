public section

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

set_option linter.unusedSectionVars false

namespace Asc77

open CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.T8YY

open scoped commutatorElement

namespace T8ZZ

open CFSG.ClassicalInvolution.Asc77.T8ZZ

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem xMem_z_K (hs : Std8 Ω K J S R T W z t) : T8.XMem Ω z K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  refine ⟨hK, ?_, R, Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1
      hs.hR.2.1, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  · have h := hs.hz.conj_eq (n := r) (conjSub_eq_self_of_mem (hs.hR.2.1 hr))
    calc r * z = (r * z * r⁻¹) * r := by group
      _ = z * r := by rw [h]

end T8ZZ
end Asc77
end
end CFSG.ClassicalInvolution.Q3.Q3T8
end
