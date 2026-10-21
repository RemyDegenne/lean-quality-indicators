namespace OAI

section

namespace CriticalHoneycomb.Transfer.Reflection

open scoped Matrix BigOperators

theorem source_boundary_pair_constant (t y : ℝ)
    (hm : Q (t-y)≠0) (hp : Q (t+y)≠0)
    (ht : sine (gamma+t)≠0) (hy : sine (gamma+y)≠0) :
    actAC (spectralR (t-y))
      (crossedBC (spectralR (b-(t+y))) (boundary0 t) (boundary0 y))=
    actBDt (spectralR (t-y))
      (crossedADt (spectralR (b-(t+y))) (boundary0 t) (boundary0 y)) := by
  apply unbend_injective
  rw [unbend_AC,unbend_BDt,unbend_BC,unbend_ADt]
  simpa only [mul_assoc] using source_reflection_constant t y hm hp ht hy

end CriticalHoneycomb.Transfer.Reflection
end
end OAI
