public section

namespace CFSG.Assembly.LargeEven

theorem largeEvenSplit_iff (p : ℕ) (lab : LargeEvenLabel) :
    LargeEvenSplit p lab ↔ CFSG.Open.GLASplit p (labelEquiv lab) :=
  Iff.rfl

end CFSG.Assembly.LargeEven
end
