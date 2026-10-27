@[expose] public section

universe u

namespace AddMonoid

variable (A : Type u) [AddMonoid A]

/-- Every positive integer supported on `S` acts surjectively on `A` by repeated addition.
This abstracts the supported-divisibility condition in Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §7, before Proposition (1.7.7), using
Mathlib’s divisibility API. -/
def IsPrimeSupportedDivisible (S : Set Nat.Primes) : Prop :=
  ∀ n : ℕ, n ∈ Nat.primeSupportedIndices S →
    Function.Surjective (fun a : A => n • a)

end AddMonoid
end
