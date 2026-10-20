@[expose] public section

namespace Descriptive.Tree

open CategoryTheory

noncomputable section «Section1»

variable {S T U : Trees} {k m n : ℕ}

universe u in

/-- A morphism is k-fixing if it is a bijection on the first k levels -/
class Fixing (k : outParam ℕ) (f : S ⟶ T) : Prop where prop : IsIso ((res k).map f)

end «Section1»
end Descriptive.Tree
end
