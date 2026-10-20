@[expose] public section

open Function (Injective Surjective)

noncomputable section

variable {p : ℕ} (n : ℕ) (R : Type*)

local notation "𝕎" => WittVector p

variable {n R}

local macro (name := witt_truncateFun_tac) "witt_truncateFun_tac" : tactic =>
  `(tactic|
    { change _ = WittVector.truncateFun n _
      apply TruncatedWittVector.out_injective
      iterate rw [WittVector.out_truncateFun]
      first
      | rw [WittVector.init_add]
      | rw [WittVector.init_mul]
      | rw [WittVector.init_neg]
      | rw [WittVector.init_sub]
      | rw [WittVector.init_nsmul]
      | rw [WittVector.init_zsmul]
      | rw [WittVector.init_pow]})

namespace WittVector

open TruncatedWittVector hiding truncate coeff

section lift

variable [CommRing R]

variable [Fact p.Prime]

variable {S : Type*} [Semiring S]

variable (f : ∀ k : ℕ, S →+* TruncatedWittVector p k R)

variable
  (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), (TruncatedWittVector.truncate hk).comp (f k₂) = f k₁)

variable (n)

/-- Given a family `fₖ : S → TruncatedWittVector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def liftFun (s : S) : 𝕎 R :=
  WittVector.mk p fun k => TruncatedWittVector.coeff (Fin.last k) (f (k + 1) s)

end lift
end WittVector
end
end
