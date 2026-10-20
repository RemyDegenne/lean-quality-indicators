@[expose] public section

open Set Real Complex Filter

open scoped Topology

namespace HurwitzZeta

lemma differentiableAt_expZeta (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ (expZeta a) s := by
  apply DifferentiableAt.add
  · exact differentiableAt_cosZeta a hs
  · apply (differentiableAt_const _).mul (differentiableAt_sinZeta a s)

end HurwitzZeta
end
