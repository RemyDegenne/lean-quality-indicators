@[expose] public section

open CategoryTheory Function Set

open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

@[simp]
theorem integerCompletionEquivPrimewisePadic_apply
    (x : integerCompletion.{u}) :
    integerCompletionEquivPrimewisePadic.{u} x =
      integerCompletionToPrimewisePadic x := by
  rfl

end ProfiniteGrp
end
