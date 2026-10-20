@[expose] public section

namespace Complexity

namespace BinaryShiftMul

theorem partialShift_full_internal (lhs rhs : ℕ) :
    partialShift lhs rhs.size = lhs * 2 ^ rhs.size := by
  rfl

end BinaryShiftMul
end Complexity
end
