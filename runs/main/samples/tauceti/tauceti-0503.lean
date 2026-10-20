public section

open scoped Nat

namespace TauCeti

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace PerfectMatching

variable {a b : α} {D : PerfectMatching α}

section Congr

theorem isPerfectMatching_permCongr (e : α ≃ β) {f : Equiv.Perm α} (hf : IsPerfectMatching f) :
    IsPerfectMatching (e.permCongr f) := by
  refine ⟨fun b => by simp [hf.1], fun b hb => hf.2 (e.symm b) ?_⟩
  simpa using congrArg e.symm hb

end Congr
end PerfectMatching
end TauCeti
end
