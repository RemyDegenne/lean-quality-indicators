public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22

open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint.NativeSporadic (Carrier)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Perm

theorem exists_fjPt_conj {n : J} (hn : n ∈ normalizer ((frameE : Subgroup J) : Set J))
    (i : Fin 23) : ∃ j, n * fjPt i * n⁻¹ = fjPt j := by
  have h1 : n * fjPt i * n⁻¹ ∈ (frameE : Subgroup J) :=
    (Subgroup.mem_normalizer_iff.1 hn _).1 (fjPt_mem_frameE i)
  have h2 : n * fjPt i * n⁻¹ ∈ D23 := conj_mem_D23 n _ (fjPt_mem i)
  obtain ⟨j, hj⟩ := mem_frameE_and_D23_iff.1 ⟨h1, h2⟩
  exact ⟨j, hj.symm⟩

end Perm
end CFSG.EvenSporadicStandard.Solomon78.F23L63
end
