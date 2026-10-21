namespace OAI

section

namespace MeanPayoff

open scoped Classical

@[simp] theorem badTimes_zero {α : Type} (bad : α → Prop) (qs : List α) (q : α) :
    badTimes bad qs q 0 = 0 := by simp [badTimes]

end MeanPayoff
end
end OAI
