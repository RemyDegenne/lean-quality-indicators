public noncomputable section

open Function Cardinal Set Order

open scoped Ordinal

universe u v w

variable {α γ : Type u} {β : Type v}

namespace Ordinal

section LinearOrder

variable [LinearOrder β] [LinearOrder γ]

theorem cof_iSup [NoMaxOrder γ] {f : γ → Ordinal} (hf : StrictMono f) :
    cof (⨆ i, f i) = Order.cof γ := by
  simpa using lift_cof_iSup hf

end LinearOrder
end Ordinal
end
