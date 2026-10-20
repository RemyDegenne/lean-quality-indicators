@[expose] public section

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool))

section Products

variable [LinearOrder I]

namespace Products

/--
The predicate on products which we prove picks out a basis of `LocallyConstant C ℤ`. We call such a
product "good".
-/
def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

end Products
end Products
end Profinite.NobelingProof
end
