@[expose] public section

namespace Multiset

section Pi

open Function

section

variable {α : Type*} [DecidableEq α] {β : α → Type*}

@[simp]
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b :=
  recOn_cons a m

end
end Pi
end Multiset
end
