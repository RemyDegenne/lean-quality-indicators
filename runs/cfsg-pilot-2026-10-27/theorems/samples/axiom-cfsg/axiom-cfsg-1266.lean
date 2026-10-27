public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitaryFourCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag LinearCover LinearFlag

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem bar_ι (x : ZMod 2) : h.bar (ι h x) = ι h x := by
  rw [bar_apply_two, sq, ι_mul_self]

end UnitaryFourCover
end CFSG.LocalAnalysis.ComponentInitial
end
