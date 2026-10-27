@[expose] public section

open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

/-- A SubMulAction is a set which is closed under scalar multiplication. -/
@[to_additive]
structure SubMulAction (R : Type u) (M : Type v) [SMul R M] : Type v where
  /-- The underlying set of a `SubMulAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

end
