namespace OAI

namespace Release075.PermCycles

open Equiv

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
theorem pow_intertwine (f : Perm A) (g : Perm B) (e : A → B)
    (he : ∀ a, e (f a) = g (e a)) (n : ℕ) (a : A) :
    e ((f^n) a) = (g^n) (e a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Perm.mul_apply,he,ih,pow_succ',Perm.mul_apply]

end Release075.PermCycles
end OAI
