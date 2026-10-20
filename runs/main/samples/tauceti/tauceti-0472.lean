public section

namespace TauCeti

open Equiv Equiv.Perm TemperleyLieb

namespace PDCode

variable {n : ℕ}

section Insert

variable (D : PDCode n) (p q : Fin (4 * n)) (b : Bool)

@[simp] theorem mirror_insertCrossing :
    (D.insertCrossing p q b).mirror = D.mirror.insertCrossing p q !b := by
  apply PDCode.ext
  · simp [insertCrossing]
  · simp [insertCrossing]
  · simp [insertCrossing]
  · funext i
    induction i using Fin.lastCases <;> simp

end Insert
end PDCode
end TauCeti
end
