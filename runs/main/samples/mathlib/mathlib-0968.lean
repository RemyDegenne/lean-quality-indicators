public section

variable {ι α β : Type*}

section LinearOrderedCommGroup

variable [Preorder α] [CommGroup β] [LinearOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α}
  {g g₁ g₂ : ι → β}

@[to_additive] lemma Antivary.mul_right (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h

end LinearOrderedCommGroup
end
