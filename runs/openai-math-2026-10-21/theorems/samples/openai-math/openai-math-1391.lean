namespace OAI

noncomputable section

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators

namespace Contingency

@[simp] theorem profileEquiv_succ (C n : ℕ) (j : Fin (C+1)) (α : Profiles C n) :
    profileEquiv C (n+1) (j,α) = Fin.cons j (profileEquiv C n α) := rfl

end Contingency
end
end OAI
