@[expose] public section

open Function

universe u

variable {α : Type u}

@[inherit_doc]
postfix:1024 "ˣ" => Units

attribute [instance] AddUnits.instNeg

@[inherit_doc]
infixl:70 " /ₚ " => divp

section IsUnit

variable {M : Type*}

@[to_additive]
theorem isUnit_iff_exists_inv [Monoid M] [IsDedekindFiniteMonoid M] {a : M} :
    IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨(·.exists_right_inv), fun ⟨b, hab⟩ ↦ .of_mul_eq_one b hab⟩

end IsUnit
end
