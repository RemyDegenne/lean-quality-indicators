@[expose] public section

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to N. -/]
def snd : α × β →*o β where
  __ := MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

end OrderMonoidHom
end
