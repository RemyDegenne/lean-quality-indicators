@[expose] public section

universe w w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

namespace Relations

variable [IsEmpty relations.R]

/-- If `relations : Relations A` involves no relations (`[IsEmpty relations.R]`),
then the free module `relations.G →₀ A` satisfies the universal property of the
corresponding module defined by generators (and relations). -/
noncomputable def solutionFinsupp.isPresentationCore :
    Solution.IsPresentationCore.{w} relations.solutionFinsupp where
  desc s := Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h

end Relations
end Module
end
