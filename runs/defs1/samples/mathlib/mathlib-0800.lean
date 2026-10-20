@[expose] public section

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool))

section Products

variable [LinearOrder I]

/--
`Products I` is the type of lists of decreasing elements of `I`, so a typical element is
`[i₁, i₂, ...]` with `i₁ > i₂ > ...`. We order `Products I` lexicographically, so `[] < [i₁, ...]`,
and `[i₁, i₂, ...] < [j₁, j₂, ...]` if either `i₁ < j₁`, or `i₁ = j₁` and `[i₂, ...] < [j₂, ...]`.

Terms `m = [i₁, i₂, ..., iᵣ]` of this type will be used to represent products of the form
`e C i₁ ··· e C iᵣ : LocallyConstant C ℤ` . The function associated to `m` is `m.eval`.
-/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.IsChain (· > ·)}

end Products
end Profinite.NobelingProof
end
