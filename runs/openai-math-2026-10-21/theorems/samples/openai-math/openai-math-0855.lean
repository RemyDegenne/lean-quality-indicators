namespace OAI

namespace QuarticPowerFree

open scoped BigOperators

open scoped BigOperators

theorem pairTranslate_injective {h : ℕ} (u v : ℕ) :
    Function.Injective (pairTranslate (h := h) u v) := by
  intro p q he
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 := congrFun he 0
    simp only [pairTranslate, Fin.cons_zero, Prod.mk.injEq] at h0
    exact Prod.ext (Nat.add_right_cancel h0.1) (Nat.add_right_cancel h0.2)
  · exact congrFun he j.succ

end QuarticPowerFree
end OAI
