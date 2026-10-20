namespace P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided

set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace K9F2

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def sig : (α × β) × γ ≃ᵐ (α × γ) × β :=
  (MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl α).prodCongr MeasurableEquiv.prodComm)).trans
    MeasurableEquiv.prodAssoc.symm

end K9F2
end
end P2MW.S_LanglandsTunnell_integrable_dualFibres_of_integrable_oneSided
