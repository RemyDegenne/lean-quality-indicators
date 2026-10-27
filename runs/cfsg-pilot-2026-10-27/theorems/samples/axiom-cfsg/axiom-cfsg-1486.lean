public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

namespace A2

theorem coeffs_eq {x : Fin 3 → Fin 3 → E} (hli : LinearIndependent E x) {a a' : Fin 3 → E}
    (h : ∑ l, a l • x l = ∑ l, a' l • x l) : a = a' := by
  funext l
  have := Fintype.linearIndependent_iff.1 hli (fun l => a l - a' l)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  exact sub_eq_zero.1 (this l)

end A2
end CFSG.GH74.Uniqueness.Bender.Frame
end
