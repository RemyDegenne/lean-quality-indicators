public noncomputable section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB

open scoped commutatorElement

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

open CFSG.Certificates (SchreierLetter)

open CFSG.Certificates.ExtraspecialNF

open CFSG.ComponentClassification.CatFactsSmall.PSp43
  (x45 y45 f45 QA45 QP45 QP45_closure QA45_closure QP45_ok QA45_ok QP45_valid QA45_valid)

theorem Ybar_le_Cbar :
    Ybar ≤ Cbar := by
  rw [Ybar, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact cGen_mem_Cbar 1
  · exact cGen_mem_Cbar 2

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
end
