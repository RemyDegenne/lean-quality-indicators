public section

open Multiset

universe u

variable {α : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

lemma cons_sdiff_cons (hab : a ≠ b) (ha hb) : s.cons a ha \ s.cons b hb = {a} := by grind

end Sdiff
end Finset
end
