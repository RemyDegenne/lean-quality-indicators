namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)

theorem skeletonD_exact (hex : ∀ n, Function.Exact (D.d (n + 1)) (D.d n)) (n : ℕ) :
    Function.Exact (skeletonD D (n + 1)) (skeletonD D n) :=
  coneBlock_exact _ _ _ _ _ _ (hex n) (middleD_exact D hex n) (attachingRow_comm D n)

end ArExplicit.TwoCone
end
end OAI
