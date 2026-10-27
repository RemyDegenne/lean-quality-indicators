public section

namespace CFSG.ComponentClassification.HSFLit.Sec5E

namespace T2M

theorem classify : ∀ ax : T2M, InT ax → ax * ax = z → ax * (t * k) = (t * k) * ax →
    ax * (z * k) = (z * k) * ax → ClY ax := by
  decide +kernel

end T2M
end CFSG.ComponentClassification.HSFLit.Sec5E
end
