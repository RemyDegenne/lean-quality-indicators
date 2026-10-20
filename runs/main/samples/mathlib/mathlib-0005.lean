@[expose] public section

open Function OrderDual

variable {α β : Type*}

section PartialOrderedSemifield

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa using inv_anti₀ ha h

end PartialOrderedSemifield
end
