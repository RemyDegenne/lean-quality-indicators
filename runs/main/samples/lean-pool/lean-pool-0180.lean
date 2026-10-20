public section

namespace ParallelPostulate

namespace Pairs

section Ring

variable {K : Type*} [CommRing K]

namespace Figure

theorem a_meets_b (F : Figure K) : F.a.pt 0 = F.b.pt 0 := by
  rw [Dim.pt_zero, Dim.pt_zero]; exact F.a0_eq_b0

end Figure
end Ring
end Pairs
end ParallelPostulate
end
