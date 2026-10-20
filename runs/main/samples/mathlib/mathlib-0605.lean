@[expose] public section

open Set

open scoped Computability

universe u v

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

variable (M) in
@[simp]
theorem reverse_reverse : M.reverse.reverse = M := by
  simp [reverse]

end NFA
end
