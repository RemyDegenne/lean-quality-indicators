@[expose] public section

open Function

variable {M₀ G₀ M₀' G₀' : Type*}

section GroupWithZero

variable [GroupWithZero G₀]

/-- Pull back a `GroupWithZero` along an injective function.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    domain_nontrivial f zero one with
    inv_zero := hf <| by rw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx => hf <| by
      rw [one, mul, inv, mul_inv_cancel₀ ((hf.ne_iff' zero).2 hx)] }

end GroupWithZero
end
