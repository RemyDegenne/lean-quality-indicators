@[expose] public section

universe u v₁ v₂ v₃

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x : ∀ i, f i) (i : I)

namespace Function

section Extend

@[to_additive (attr := simp)]
theorem Injective.extend_mulSingle [DecidableEq α] [DecidableEq β] [One γ] {f : α → β}
    (hf : Injective f) (i : α) (a : γ) :
    extend f (Pi.mulSingle i a) 1 = Pi.mulSingle (f i) a := by
  simp [Pi.mulSingle, hf.extend_update]

end Extend
end Function
end
