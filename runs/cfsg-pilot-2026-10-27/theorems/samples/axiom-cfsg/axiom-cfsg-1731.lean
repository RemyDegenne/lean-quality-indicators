public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K]

variable {σ : K ≃+* K}

namespace WittData

variable (W : WittData σ) {m : ℕ}

@[simp] theorem hypA_one : W.hypA m 1 = W.u := by simp [hypA]

end WittData
end CFSG.ClassicalGroups.Unitary
end
