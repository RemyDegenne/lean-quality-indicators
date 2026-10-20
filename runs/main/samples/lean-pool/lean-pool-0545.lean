@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Johnson

section

open scoped BigOperators InnerProductSpace Matrix

theorem card_le_shellCodeNumber {n w d : ℕ}
    (C : Finset (BinaryWord n))
    (hweight : C ⊆ weightShell n w) (hC : IsBinaryCode d C) :
    C.card ≤ shellCodeNumber n w d := by
  exact Finset.le_sup ((mem_shellCodeFamily C).mpr ⟨hweight, hC⟩)

end
end Johnson
end MetricCodes
end MetricCodesNoncomputable
end
