@[expose] public section

set_option autoImplicit true

namespace Random

variable [Monad m]

/-- Generate a random value of type `α` between `x` and `y` inclusive. -/
def randBound (α : Type u)
    [Preorder α] [BoundedRandom m α] (lo hi : α) (h : lo ≤ hi) [RandomGen g] :
    RandGT g m {a // lo ≤ a ∧ a ≤ hi} :=
  (BoundedRandom.randomR lo hi h : RandGT g _ _)

end Random
end
