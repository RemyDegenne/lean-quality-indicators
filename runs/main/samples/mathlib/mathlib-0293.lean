@[expose] public section

open Function

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

infixr:25 " →*₀ " => MonoidWithZeroHom

namespace MonoidWithZeroHom

variable [FunLike F α β]

lemma copy_eq (f : α →*₀ β) (f' : α → β) (h) : f.copy f' h = f := DFunLike.ext' h

end MonoidWithZeroHom
end
